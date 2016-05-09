-- | Compose chains of functions with constant memory use

module Feldspar.Brick where



import qualified Prelude
import Control.Monad

import Data.Monoid
import qualified Data.Foldable as Foldable

import Feldspar.Run



quot :: (Prelude.Integral a, Type a) => Data a -> Data a -> Data a
quot = Prelude.error "TODO"

sizeOf :: Storable a => a -> ()
sizeOf = Prelude.error "TODO"

newStore :: MonadComp m => () -> m (Store s)
newStore = Prelude.error "TODO"

-- | Swap the contents of two stores
--
-- The implementation may use aliasing to perform the swap without copying. This
-- means that the operation can result in invalid stores, e.g. if a
-- stack-allocated store is swapped with a store that has a larger scope.
unsafeSwapStore :: Storable s => Store s -> Store s -> Run ()
unsafeSwapStore = copyStore

newtype Brick m s a = Brick
    { unBrick :: Store s -> Store s -> m (a,Bool) }

instance (Monad m, Monoid a) => Monoid (Brick m s a)
  where
    mempty = Brick $ \prev free -> return (mempty,False)
    mappend b1 b2 = Brick $ \prev free -> do
        (a,odd1) <- unBrick b1 prev free
        let (p,f) = if odd1 then (free,prev) else (prev,free)
        (b,odd2) <- unBrick b2 p f
        return (mappend a b, odd1 Prelude./= odd2)

instance Monad m => Functor (Brick m s)
  where
    fmap f brick = Brick $ \prev free -> do
        (a,odd) <- unBrick brick prev free
        return (f a, odd)

-- | Run a 'Brick' computation. This function will allocate one extra 'Store' of
-- the same size as the input value.
runBrick :: (MonadComp m, Storable s) => Brick m s a -> s -> m (s,a)
runBrick brick s = do
    s1 <- initStore s
    s2 <- newStore (sizeOf s)
    (a,odd) <- unBrick brick s1 s2
    r <- readStore $ if odd then s2 else s1
      -- TODO freeStore $ if odd then s1 else s2
    return (r,a)
  -- TODO What if one wants a bigger store?

forget :: (Monad m, Monoid b) => Brick m s a -> Brick m s b
forget = fmap (const mempty)

-- | Make a 'Brick' from a function
funBrick :: (MonadComp m, Storable s) => (s -> (s,a)) -> Brick m s a
funBrick f = Brick $ \prev free -> do
    s <- readStore prev
    let (s',a) = f s
    writeStore free s'
    return (a,True)

-- | Make a 'Brick' from a function
funBrick' :: (MonadComp m, Storable s, Monoid a) => (s -> s) -> Brick m s a
funBrick' f = funBrick (\s -> let s' = f s in (s',mempty))

unroll :: (Monad m, Storable s, Monoid a) =>
    Int -> (Int -> Brick m s a) -> Brick m s a
unroll n body = Foldable.fold $ Prelude.map body $ Prelude.take n [0..]

forBrick :: (Storable s, Monoid b) =>
    Data Length -> (Data Index -> Brick Run s a) -> Brick Run s b
forBrick len body = Brick $ \prev free -> do
    for (0, 1, Excl len) $ \i -> do
      (_,odd) <- unBrick (body i) prev free
      when odd $ unsafeSwapStore prev free
    return (mempty,False)

