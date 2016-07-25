-- Feldspar-specific verification bits (expression evaluation).
module Feldspar.Verify.Representation where

import Language.Embedded.Verify hiding (ite)
import Language.SMTLib2 hiding (SMTExpr, SMTType, SMTOrd(..), Args, (.==.))
import Language.SMTLib2.Internals hiding (SMTExpr, SMTType, SMTOrd(..), Args, (.==.))
import qualified Language.SMTLib2 as SMT
import Feldspar.Primitive.Representation
import Language.Syntactic
import Data.Constraint(Dict(..))
import Data.Int
import Data.Word
import Data.Complex
import Data.Typeable
import Language.Embedded.Imperative.CMD
import Language.Embedded.Verify.Arithmetic
import Data.Void
import Control.Monad
import Control.Monad.Trans

instance SMTEval1 Prim where
  type Pred Prim = PrimType'
  newtype SMTExpr Prim Bool = Bool (SMT.SMTExpr Bool)
    deriving Typeable
  newtype SMTExpr Prim Float = Float (SMT.SMTExpr Rational)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Double = Double (SMT.SMTExpr Rational)
    deriving (Typeable, Num, SMTOrd)
  -- We don't support complex arithmetic yet, these are stubs.
  newtype SMTExpr Prim (Complex Float) = CFloat Void
    deriving Typeable
  newtype SMTExpr Prim (Complex Double) = CDouble Void
    deriving Typeable
  newtype SMTExpr Prim Int8   = Int8   (Signed N8)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Int16  = Int16  (Signed N16)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Int32  = Int32  (Signed N32)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Int64  = Int64  (Signed N64)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Word8  = Word8  (Unsigned N8)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Word16 = Word16 (Unsigned N16)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Word32 = Word32 (Unsigned N32)
    deriving (Typeable, Num, SMTOrd)
  newtype SMTExpr Prim Word64 = Word64 (Unsigned N64)
    deriving (Typeable, Num, SMTOrd)

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
  Bool x .<.  Bool y = not' x .&&. y
  Bool x .>.  Bool y = x .&&. not' y
  Bool x .<=. Bool y = not' x .||. y
  Bool x .>=. Bool y = x .||. not' y
instance SMTOrd (SMT.SMTExpr Rational)

instance Fresh (SMTExpr Prim Bool)   where fresh = fmap Bool   . fresh
instance Fresh (SMTExpr Prim Int8)   where fresh = fmap Int8   . fresh
instance Fresh (SMTExpr Prim Int16)  where fresh = fmap Int16  . fresh
instance Fresh (SMTExpr Prim Int32)  where fresh = fmap Int32  . fresh
instance Fresh (SMTExpr Prim Int64)  where fresh = fmap Int64  . fresh
instance Fresh (SMTExpr Prim Word8)  where fresh = fmap Word8  . fresh
instance Fresh (SMTExpr Prim Word16) where fresh = fmap Word16 . fresh
instance Fresh (SMTExpr Prim Word32) where fresh = fmap Word32 . fresh
instance Fresh (SMTExpr Prim Word64) where fresh = fmap Word64 . fresh
instance Fresh (SMTExpr Prim Float)  where fresh = fmap Float   . fresh
instance Fresh (SMTExpr Prim Double) where fresh = fmap Double   . fresh
instance Fresh (SMTExpr Prim (Complex Float))  where fresh = fmap CFloat  . fresh
instance Fresh (SMTExpr Prim (Complex Double)) where fresh = fmap CDouble . fresh

instance SMTEval Prim Bool where
  type SMTType Prim Bool = Bool
  toSMT (Bool x) = x
  fromSMT = Bool
  fromConstant = Bool . constant
  witnessOrd _ = Dict

instance SMTEval Prim Int8 where
  type SMTType Prim Int8 = BV8
  toSMT (Int8 (Signed x)) = x
  fromSMT = Int8 . Signed
  fromConstant = Int8 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int16 where
  type SMTType Prim Int16 = BV16
  toSMT (Int16 (Signed x)) = x
  fromSMT = Int16 . Signed
  fromConstant = Int16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int32 where
  type SMTType Prim Int32 = BV32
  toSMT (Int32 (Signed x)) = x
  fromSMT = Int32 . Signed
  fromConstant = Int32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int64 where
  type SMTType Prim Int64 = BV64
  toSMT (Int64 (Signed x)) = x
  fromSMT = Int64 . Signed
  fromConstant = Int64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word8 where
  type SMTType Prim Word8 = BV8
  toSMT (Word8 (Unsigned x)) = x
  fromSMT = Word8 . Unsigned
  fromConstant = Word8 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word16 where
  type SMTType Prim Word16 = BV16
  toSMT (Word16 (Unsigned x)) = x
  fromSMT = Word16 . Unsigned
  fromConstant = Word16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word32 where
  type SMTType Prim Word32 = BV32
  toSMT (Word32 (Unsigned x)) = x
  fromSMT = Word32 . Unsigned
  fromConstant = Word32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word64 where
  type SMTType Prim Word64 = BV64
  toSMT (Word64 (Unsigned x)) = x
  fromSMT = Word64 . Unsigned
  fromConstant = Word64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Float where
  type SMTType Prim Float = Rational
  toSMT (Float x) = x
  fromSMT = Float
  fromConstant = Float . fromRational . toRational
  witnessOrd      _ = Dict
  witnessNum _ = Dict

instance SMTEval Prim Double where
  type SMTType Prim Double = Rational
  toSMT (Double x) = x
  fromSMT = Double
  fromConstant = Double . fromRational . toRational
  witnessOrd      _ = Dict
  witnessNum _ = Dict

instance SMTEval Prim (Complex Float) where
  type SMTType Prim (Complex Float) = Void
  toSMT (CFloat x) = absurd x
  fromSMT = error "complex numbers not supported"
  fromConstant = error "complex numbers not supported"
  witnessOrd _ = error "complex numbers not supported"
  witnessNum _ = error "complex numbers not supported"

instance SMTEval Prim (Complex Double) where
  type SMTType Prim (Complex Double) = Void
  toSMT (CDouble x) = absurd x
  fromSMT = error "complex numbers not supported"
  fromConstant = error "complex numbers not supported"
  witnessOrd _ = error "complex numbers not supported"
  witnessNum _ = error "complex numbers not supported"

instance Fresh Void where fresh = error "complex numbers not supported"
instance SMTValue Void where
  mangle = error "complex numbers not supported"
  unmangle = error "complex numbers not supported"

instance SMT.SMTType Void where
  type SMTAnnotation Void = ()
  getSort x _ = absurd x
  asValueType x _ _ = absurd x
  annotationFromSort x _ = absurd x
  defaultExpr = error "complex numbers not supported"

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
    bvToRealFun <- global "bv-to-real"
    fmap (i2n (app bvToRealFun)) (eval (Prim x))
primEval I2B ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessNum (undefined :: Prim b) = do
    x <- eval (Prim x)
    return (fromSMT (not' (x .==. 0)))
primEval B2I (x :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) = do
    x <- eval (Prim x)
    return (smtIte (toSMT x) 1 0)
primEval Not (x :* Nil) =
  fmap (fromSMT . not' . toSMT) (eval (Prim x))
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
    x ./=. y = not' (x .==. y)
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
  return (fromSMT (select (arr_value arr) (toSMT i)))
primEval Cond (cond :* x :* y :* Nil) =
  liftM3 smtIte (fmap toSMT (eval (Prim cond))) (eval (Prim x)) (eval (Prim y))
primEval exp _ = error ("Unimplemented: " ++ show exp)

-- NB we don't use this because it's too expensive.
-- Instead, int-to-rational conversion is left unspecified.
bvToReal :: SMT.SMTExpr BV64 -> SMT.SMTExpr Rational
bvToReal x =
  sum [SMT.ite (bvand x (fromInteger (2^i)) SMT..==. 0) 0 (2^i) | i <- [0..63]]

i2n ::
  (SMTEval Prim a, SMTEval Prim b, PrimType' a, PrimType' b, Integral a, Num b) =>
  (SMT.SMTExpr BV64 -> SMT.SMTExpr Rational) ->
  SMTExpr Prim a -> SMTExpr Prim b
i2n bvToReal = fromBV64 . toBV64
  where
    fromBV64 :: forall a. (SMTEval Prim a, PrimType' a, Num a) => SMT.SMTExpr BV64 -> SMTExpr Prim a
    fromBV64 x =
      case primTypeRep :: PrimTypeRep a of
        Int8T    -> let (_, _, _, _, _, _, _, y) = bvsplitu64to8  x in fromSMT y
        Int16T   -> let             (_, _, _, y) = bvsplitu64to16 x in fromSMT y
        Int32T   -> let                   (_, y) = bvsplitu64to32 x in fromSMT y
        Int64T   -> fromSMT x
        Word8T   -> let (_, _, _, _, _, _, _, y) = bvsplitu64to8  x in fromSMT y
        Word16T  -> let             (_, _, _, y) = bvsplitu64to16 x in fromSMT y
        Word32T  -> let                   (_, y) = bvsplitu64to32 x in fromSMT y
        Word64T  -> fromSMT x
        FloatT   -> fromSMT (bvToReal x)
        DoubleT  -> fromSMT (bvToReal x)
        ComplexFloatT  -> error "complex numbers not supported"
        ComplexDoubleT -> error "complex numbers not supported"

    toBV64 :: (SMTEval Prim a, PrimType' a, Integral a) => SMTExpr Prim a -> SMT.SMTExpr BV64
    toBV64 (x :: SMTExpr Prim a) =
      case primTypeRep :: PrimTypeRep a of
        Int8T   -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N56))) (toSMT x)
        Int16T  -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N48))) (toSMT x)
        Int32T  -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N32))) (toSMT x)
        Int64T  -> toSMT x
        Word8T  -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N56))) (toSMT x)
        Word16T -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N48))) (toSMT x)
        Word32T -> bvconcat (0 :: SMT.SMTExpr (BitVector (BVTyped N32))) (toSMT x)
        Word64T -> toSMT x

withFeldsparGlobals :: Verify a -> Verify a
withFeldsparGlobals mx = do
  bvToReal <- lift fun :: Verify (SMTFunction (SMT.SMTExpr BV64) Rational)
  withGlobals [("bv-to-real", Global bvToReal)] mx
