{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

This module defines 'FixedStorableArray', a simple wrapper around
'StorableArray' with its dimensions encoded in the
type. 'FixedStorableArray' provides a 'Storable' instance that uses
the type-level dimensions, and significantly eases writing FFI
bindings to fixed-size native arrays. For example,
@'FixedStorableArray' 10 CInt@ has a 'Storable' instance that is
directly compatible with @int foo[10]@ in native code.

Multidimensional native arrays are also
supported. @'FixedStorableArray' \'(10,20,100) CUChar@ is compatible
with @unsigned char foo[10][20][100]@. Note the leading @\'@ before
the tuple containing the dimensions. It marks it as a @DataKinds@
lifted tuple, necessary to store the dimensions.

To operate on the contents of a 'FixedStorableArray', use
'toStorableArray'. 'toStorableArray' returns a 'StorableArray' with
the correct type and index values already in place. For example, the
result of 'toStorableArray' on a @'FixedStorableArray' \'(10,20,100)
CUChar@ is a @'StorableArray' (Int, Int, Int) CUChar@ with its bounds
set to @((0,0,0),(9,19,99))@.

-}
module Foreign.Marshal.FixedStorableArray
       ( FixedStorableArray
       , newFixedStorableArray
       , newFixedStorableArray_
       , toStorableArray
       , HasBounds(..)
       , fromNat
       ) where

import GHC.TypeLits

import Data.Array.Storable
import Data.Functor          ((<$>))
import Data.Proxy            (Proxy(..))

import Foreign.Storable      (Storable(..))
import Foreign.Marshal.Array (copyArray)
import Foreign.Ptr           (castPtr)


-- | A minimal wrapper for 'StorableArray' that encodes the full
-- dimensions of the array in the type. Intended for interfacing with
-- (possibly-)multidimensional arrays of fixed size in native code.
newtype FixedStorableArray dimensions e =
    FixedStorableArray {
        -- | Returns the backing 'StorableArray' of this
        -- 'FixedStorableArray'. The backing array is shared such that
        -- modifications to it will be seen across all uses of this
        -- 'FixedStorableArray'.
        toStorableArray :: StorableArray (Bound dimensions) e }

-- | This class connects dimension description types with
-- 'StorableArray' index types and values. Instances are provided for
-- up to 13 dimensions. More can be added if there's any need.
class HasBounds d where
    -- | The bounding type for this dimension description
    type Bound d :: *
    -- | The concrete bounds for this dimension
    bounds :: FixedStorableArray d e -> (Bound d, Bound d)

-- | Create a 'FixedStorableArray' and populate it with copies of the
-- element passed in. Dimensions will be determined from the return
-- type.
newFixedStorableArray :: (HasBounds d, Ix (Bound d), Storable e) =>
                         e -> IO (FixedStorableArray d e)
newFixedStorableArray x = do
    rec let b = bounds ma
        ma <- FixedStorableArray <$> newArray b x
    return ma

-- | Create a 'FixedStorableArray' and don't populate it with anything
-- in particular. Contents may or may not be initialized to anything
-- at all. Dimensions will be determined from the return type.
newFixedStorableArray_ :: (HasBounds d, Ix (Bound d), Storable e) =>
                          IO (FixedStorableArray d e)
newFixedStorableArray_ = do
    rec let b = bounds ma
        ma <- FixedStorableArray <$> newArray_ b
    return ma

instance (HasBounds d, Ix (Bound d), Storable e) =>
         Storable (FixedStorableArray d e) where
    sizeOf a = sizeOf (undefined :: e) * rangeSize (bounds a)
    alignment _ = alignment (undefined :: e)
    peek src' = do
        ma <- newFixedStorableArray_
        let sa = toStorableArray ma
            src = castPtr src'
        count <- rangeSize <$> getBounds sa
        withStorableArray sa $ \dst -> copyArray dst src count
        return ma
    poke dst' ma = do
        let sa = toStorableArray ma
            dst = castPtr dst'
        count <- rangeSize <$> getBounds sa
        withStorableArray sa $ \src -> copyArray dst src count


-- | A conversion function for converting type-level naturals to
-- value-level. This is being exposed to aid in the creation of
-- additional 'HasBounds' instances for those who might desire to do
-- so.
--
-- Haddock is currently eating the important qualification that the
-- type variable @n@ must have the kind 'Nat'. The 'SingI' instance is
-- automatically fulfilled for all types of kind 'Nat'. Its explicit
-- presence in the signature is an artifact of how GHC implements
-- dictionary passing and type erasure.
fromNat :: forall (proxy :: Nat -> *) (n :: Nat). SingI n => proxy n -> Int
fromNat _ = fromInteger $ fromSing (sing :: Sing n)


----------------------------------------------------------------------------
-- HasBounds instances. More can be written, trivially - it's just a matter
-- of whether they'll ever actually be used.

instance SingI a => HasBounds (a :: Nat) where
    type Bound (a) = Int
    bounds _ = (0, fromNat (Proxy :: Proxy a) - 1)

instance (SingI a, SingI b) => HasBounds ('(a, b) :: (Nat, Nat)) where
    type Bound '(a, b) = (Int, Int)
    bounds _ = ((0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1))

instance (SingI a, SingI b, SingI c) =>
         HasBounds ('(a, b, c) :: (Nat, Nat, Nat)) where
    type Bound '(a, b, c) = (Int, Int, Int)
    bounds _ = ((0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1))

instance (SingI a, SingI b, SingI c, SingI d) =>
         HasBounds ('(a, b, c, d) :: (Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d) = (Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e) =>
         HasBounds ('(a, b, c, d, e) :: (Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e) = (Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f) =>
         HasBounds ('(a, b, c, d, e, f) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e, f) = (Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g) =>
         HasBounds ('(a, b, c, d, e, f, g) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e, f, g) = (Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h) =>
         HasBounds ('(a, b, c, d, e, f, g, h) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e, f, g, h) =
        (Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i) =>
         HasBounds ('(a, b, c, d, e, f, g, h, i) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e, f, g, h, i) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1,
                 fromNat (Proxy :: Proxy i) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j) =>
         HasBounds ('(a, b, c, d, e, f, g, h, i, j) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat)) where
    type Bound '(a, b, c, d, e, f, g, h, i, j) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1,
                 fromNat (Proxy :: Proxy i) - 1,
                 fromNat (Proxy :: Proxy j) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k) =>
         HasBounds ('(a, b, c, d, e, f, g, h, i, j, k) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat))
      where
    type Bound '(a, b, c, d, e, f, g, h, i, j, k) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1,
                 fromNat (Proxy :: Proxy i) - 1,
                 fromNat (Proxy :: Proxy j) - 1,
                 fromNat (Proxy :: Proxy k) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k, SingI l) =>
         HasBounds ('(a, b, c, d, e, f, g, h, i, j, k, l) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat,
                     Nat)) where
    type Bound '(a, b, c, d, e, f, g, h, i, j, k, l) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1,
                 fromNat (Proxy :: Proxy i) - 1,
                 fromNat (Proxy :: Proxy j) - 1,
                 fromNat (Proxy :: Proxy k) - 1,
                 fromNat (Proxy :: Proxy l) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k, SingI l, SingI m) =>
         HasBounds ('(a, b, c, d, e, f, g, h, i, j, k, l, m) ::
                    (Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat, Nat,
                     Nat, Nat)) where
    type Bound '(a, b, c, d, e, f, g, h, i, j, k, l, m) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (Proxy :: Proxy a) - 1,
                 fromNat (Proxy :: Proxy b) - 1,
                 fromNat (Proxy :: Proxy c) - 1,
                 fromNat (Proxy :: Proxy d) - 1,
                 fromNat (Proxy :: Proxy e) - 1,
                 fromNat (Proxy :: Proxy f) - 1,
                 fromNat (Proxy :: Proxy g) - 1,
                 fromNat (Proxy :: Proxy h) - 1,
                 fromNat (Proxy :: Proxy i) - 1,
                 fromNat (Proxy :: Proxy j) - 1,
                 fromNat (Proxy :: Proxy k) - 1,
                 fromNat (Proxy :: Proxy l) - 1,
                 fromNat (Proxy :: Proxy m) - 1))

instance SingI n => HasBounds ('[n] :: [Nat]) where
    type Bound ('[n]) = Int
    bounds _ = (0, fromNat (Proxy :: Proxy n) - 1)

instance (SingI n, HasBounds (n2 ': ns)) =>
         HasBounds ((n ': n2 ': ns) :: [Nat]) where
    type Bound (n ': n2 ': ns) = (Int, Bound (n2 ': ns))
    bounds _ = ((0, b0), (fromNat (Proxy :: Proxy n) - 1, bn))
      where
        (b0, bn) = bounds (undefined :: FixedStorableArray (n2 ': ns) ())
