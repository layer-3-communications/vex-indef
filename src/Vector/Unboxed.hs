{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language ExplicitNamespaces #-}
{-# language GADTSyntax #-}
{-# language KindSignatures #-}
{-# language MagicHash #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}
{-# language UnboxedTuples #-}

-- Many operatations defined in this module are those
-- that are considered primitive. That is, they cannot be
-- defined in terms of other operations on length-indexed
-- vectors. Others are non-primitive.
module Vector.Unboxed
  ( -- Types
    Vector
  , MutableVector
    -- Create
  , uninitialized
    -- Index
  , index
  , read
  , write
    -- Ranges
  , copy
  , copyMutable
  , set
    -- Resize
  , shrink
    -- Freeze
  , unsafeFreeze
    -- Equality
  , equals
    -- Substitution
  , substitute
    -- Conversion
  , expose
  , exposeMutable
  , unsafeCast
  , unsafeCastMutable
    -- Specialized runST
  , runST
    -- Conversion
  , fromListN
  ) where

import Prelude hiding (read)

import Element (T)
import Array (A,M,unsafeFreeze#)
import GHC.Exts (Int(I#))
import GHC.ST (ST(ST))
import Data.Kind (Type)
import GHC.TypeNats (KnownNat,type (+))
import Arithmetic.Unsafe (type (<=)(Lte))
import Arithmetic.Unsafe (Nat(Nat),type (<)(Lt),type (:=:)(Eq))
import Arithmetic.Types (Fin(Fin))
import Control.Monad.Trans.Maybe (MaybeT(MaybeT),runMaybeT)
import Control.Monad.Trans.Class (lift)

import qualified Control.Monad.ST
import qualified GHC.Exts as Exts
import qualified GHC.TypeNats as GHC
import qualified Element as E
import qualified Array as A
import qualified Arithmetic.Nat as Nat
import qualified Arithmetic.Fin as Fin

newtype Vector :: GHC.Nat -> Type where
  Vector :: A -> Vector n

newtype MutableVector :: Type -> GHC.Nat -> Type where
  MutableVector :: M s -> MutableVector s n

uninitialized :: Nat n -> ST s (MutableVector s n)
{-# inline uninitialized #-}
uninitialized (Nat (I# n)) = ST
  ( \s0 -> case E.uninitialized# n s0 of
    (# s1, arr #) -> (# s1, MutableVector (A.liftMutable arr) #)
  )

set :: 
     (doff + n <= dlen)
  -> MutableVector s dlen -- ^ Destination
  -> Nat doff
  -> Nat n
  -> T
  -> ST s ()
{-# inline set #-}
set Lte (MutableVector dst) (Nat (I# off)) (Nat (I# len)) b = ST
  (\s0 -> case E.set# (A.unliftMutable dst) off len (E.unlift b) s0 of
    s1 -> (# s1, () #)
  )

index ::
     (m < n) -- ^ Evidence the index is in-bounds
  -> Vector n -- ^ Array
  -> Nat m -- ^ Index
  -> T
{-# inline index #-}
index Lt (Vector arr) (Nat (I# i)) = E.lift (E.index# (A.unlift arr) i)

read ::
     (m < n) -- ^ Evidence the index is in-bounds
  -> MutableVector s n -- ^ Array
  -> Nat m -- ^ Index
  -> ST s T
{-# inline read #-}
-- this is a core operation
read Lt (MutableVector arr) (Nat (I# i)) = ST
  (\s0 -> case E.read# (A.unliftMutable arr) i s0 of
    (# s1, val #) -> (# s1, E.lift val #)
  )

write ::
     (m < n) -- ^ Evidence the index is in-bounds
  -> MutableVector s n -- ^ Array
  -> Nat m -- ^ Index
  -> T
  -> ST s ()
{-# inline write #-}
-- this is a core operation
write Lt (MutableVector arr) (Nat (I# i)) x = ST
  (\s0 -> case E.write# (A.unliftMutable arr) i (E.unlift x) s0 of
    s1 -> (# s1, () #)
  )

copy ::
     (doff + n <= dlen)
  -> (soff + n <= slen)
  -> MutableVector s dlen -- ^ Destination
  -> Nat doff
  -> Vector slen -- ^ Source
  -> Nat soff
  -> Nat n
  -> ST s ()
{-# inline copy #-}
copy Lte Lte (MutableVector dst) (Nat (I# doff)) (Vector src) (Nat (I# soff)) (Nat (I# len)) = ST
  (\s0 -> (# E.copy# (A.unliftMutable dst) doff (A.unlift src) soff len s0, () #)
  )

copyMutable ::
     (doff + n <= dlen)
  -> (soff + n <= slen)
  -> MutableVector s dlen -- ^ Destination
  -> Nat doff
  -> MutableVector s slen -- ^ Source
  -> Nat soff
  -> Nat n
  -> ST s ()
{-# inline copyMutable #-}
copyMutable Lte Lte (MutableVector dst) (Nat (I# doff)) (MutableVector src) (Nat (I# soff)) (Nat (I# len)) = ST
  (\s0 -> (# E.copyMutable# (A.unliftMutable dst) doff (A.unliftMutable src) soff len s0, () #)
  )

-- | Shrink the argument vector, possibly in-place. The argument vector
-- must not be reused after being passed to this function.
shrink ::
     (m <= n)
  -> Nat m
  -> MutableVector s n -- ^ Vector to shrink
  -> ST s (MutableVector s m)
{-# inline shrink #-}
shrink Lte (Nat (I# sz)) (MutableVector x) = ST
  (\s0 -> case E.shrink# (A.unliftMutable x) sz s0 of
    (# s1, y #) -> (# s1, MutableVector (A.liftMutable y) #)
  )

-- | Freeze the mutable vector. The argument must not be reused after
-- this function is called on it. 
unsafeFreeze ::
     MutableVector s n
  -> ST s (Vector n)
{-# inline unsafeFreeze #-}
unsafeFreeze (MutableVector marr) = ST
  (\s0 -> case unsafeFreeze# (A.unliftMutable marr) s0 of
    (# s1, arr #) -> (# s1, Vector (A.lift arr) #)
  )

-- | Swap out the size with another number known to be equal.
substitute :: n :=: m -> Vector n -> Vector m
{-# INLINE substitute #-}
substitute Eq (Vector x) = Vector x

-- | Compare two vectors for equality.
--
-- Note: This is only primitive because we want to use compareByteArrays#
-- to accelerate the check. It makes the assumption that equal elements
-- are always be byte-wise equal.
--
-- Note: The above note is out of date. Fast equality checks may be reinstated
-- in the future.
equals :: Nat n -> Vector n -> Vector n -> Bool
{-# inline equals #-}
equals (Nat n) (Vector x) (Vector y) = go (n - 1)
  where
  go !ix@(I# ix#) = if ix >= 0
    then case E.eq# (E.index# (A.unlift x) ix# ) (E.index# (A.unlift y) ix# ) of
      1# -> go (ix - 1)
      _ -> False
    else True

expose :: Vector n -> A
{-# inline expose #-}
expose (Vector x) = x

exposeMutable :: MutableVector s n -> M s
{-# inline exposeMutable #-}
exposeMutable (MutableVector x) = x

-- | This is very unsafe. It is useful for interoperation with libraries
-- that return @ByteArray@ or @PrimArray@ and provide untyped (written in
-- the documentation rather than in types) guarantees about their sizes.
unsafeCast :: A -> Vector n
{-# inline unsafeCast #-}
unsafeCast = Vector

unsafeCastMutable :: M s -> MutableVector s n
{-# inline unsafeCastMutable #-}
unsafeCastMutable = MutableVector

runST :: (forall s. ST s (Vector n)) -> Vector n
{-# inline runST #-}
runST f = Vector
  (A.lift (Exts.runRW# (\s0 -> case f of { ST g -> case g s0 of { (# _, Vector r #) -> A.unlift r }})))

fromListN :: Nat n -> [T] -> Maybe (Vector n)
fromListN !n xs0 = Control.Monad.ST.runST $ runMaybeT $ do
  marr <- lift (uninitialized n)
  _ <- Fin.ascendM n xs0
    (\(Fin ix lt) xs -> case xs of
      [] -> MaybeT (pure Nothing)
      y : ys -> do
        lift (write lt marr ix y)
        pure ys
    )
  output <- lift (unsafeFreeze marr)
  pure output

instance KnownNat n => Show (Vector n) where
  showsPrec !_ !v s0 = case Nat.demote sz of
    0 -> '[':']':s0
    _ -> '[': Fin.descend sz (']':s0) (\(Fin ix lt) s -> E.shows (index lt v ix) (',':s))
    where
    sz = Nat.constant @n

instance KnownNat n => Eq (Vector n) where
  (==) = equals (Nat.constant @n)
