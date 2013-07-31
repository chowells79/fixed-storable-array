{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-|

This module exposes 'FixedStorableArray', a simple wrapper around
'StorableArray' that uses the @DataKinds@ extension to get type-level
numeric literals. These allow dimensions to be fully set by the type
at compile time. This has the added benefit of providing a 'Storable'
instance that significantly eases writing FFI bindings to fixed-size
native arrays.

For example, @'FixedStorableArray' ('N' 10) CInt@ has
a 'Storable' instance that is directly compatible with @int foo[10]@
in native code.

Multidimensional native arrays are also
supported. @'FixedStorableArray' ('N' 10, 'N' 20, 'N' 100) CUChar@ is compatible with @unsigned char foo[10][20][100]@.

Other than the 'Storable' instance, 'newFixedStorableArray', and
'newFixedStorableArray_', the only way to work with a
'FixedStorableArray' is to use 'toStorableArray' and operate on the
underlying 'StorableArray'. 'toStorableArray' generates a
'StorableArray' with the correct type and index values already in
place. For instance, the result of 'toStorableArray' on a
@'FixedStorableArray' ('N' 10, 'N' 20, 'N' 100) CUChar@ is a
@'StorableArray' (Int, Int, Int) CUChar@ with its bounds set
to @((0,0,0),(9,19,99))@.

-}
module Data.Array.FixedStorableArray
       ( FixedStorableArray
       , newFixedStorableArray
       , newFixedStorableArray_
       , toStorableArray
       , N(..)
       , fromNat
       , Bounds(..)
       ) where

import GHC.TypeLits

import Data.Array.Storable
import Data.Functor          ((<$>))

import Foreign.Storable      (Storable(..))
import Foreign.Marshal.Array (copyArray)
import Foreign.Ptr           (castPtr)


-- | This is a simple proxy type for type-level naturals. All
-- dimension types use this type to store the size along that
-- dimension.
data N (n :: Nat) = N deriving (Eq, Ord, Enum)
instance SingI n => Show (N n) where
    show N = "<N " ++ show (fromNat (N :: N n)) ++ ">"

-- | A conversion function for converting type-level naturals to
-- value-level. This is being exposed to aid in the creation of
-- additional 'Bounds' instances for those who might desire to do
-- so. Haddock is currently eating the important qualification that
-- the type variable @n@ must have the kind 'Nat'.
fromNat :: forall (proxy :: Nat -> *) (n :: Nat). SingI n => proxy n -> Int
fromNat _ = fromInteger $ fromSing (sing :: Sing n)


-- | A minimal wrapper for 'StorableArray' that encodes the full
-- dimensions of the array in the type. Intended for interfacing with
-- (possibly-)multidimensional arrays of fixed size in native code. To
-- get most functionality, use 'toStorableArray'.
newtype FixedStorableArray dimensions e =
    FixedStorableArray {
        -- | Returns the backing 'StorableArray' of this
        -- 'FixedStorableArray'. The backing array is shared across
        -- all invocations of this. Modifications to it will be seen
        -- across all uses of this 'FixedStorableArray'.
        toStorableArray :: StorableArray (Bound dimensions) e }

-- | This class connects dimension descriptions with 'StorableArray'
-- index types and values.
class Bounds d where
    -- | The bounding type for this dimension description
    type Bound d :: *
    -- | The concrete bounds for this dimension
    bounds :: FixedStorableArray d e -> (Bound d, Bound d)

-- | Create a 'FixedStorableArray' and populate it with copies of the
-- element passed in. Dimensions will be determined from the return
-- type.
newFixedStorableArray :: (Bounds d, Ix (Bound d), Storable e) =>
                         e -> IO (FixedStorableArray d e)
newFixedStorableArray x = do
    rec let b = bounds ma
        ma <- FixedStorableArray <$> newArray b x
    return ma

-- | Create a 'FixedStorableArray' and don't populate it with anything
-- in particular. Contents may or may not be initialized to anything
-- at all. Dimensions will be determined from the return type.
newFixedStorableArray_ :: (Bounds d, Ix (Bound d), Storable e) =>
                          IO (FixedStorableArray d e)
newFixedStorableArray_ = do
    rec let b = bounds ma
        ma <- FixedStorableArray <$> newArray_ b
    return ma

instance (Bounds d, Ix (Bound d), Storable e) =>
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


----------------------------------------------------------------------------
-- Bounds instances. More can be written, trivially - it's just a matter
-- of whether they'll ever actually be used.

instance SingI a => Bounds (N a) where
    type Bound (N a) = Int
    bounds _ = (0, fromNat (N :: N a) - 1)

instance (SingI a, SingI b) => Bounds (N a, N b) where
    type Bound (N a, N b) = (Int, Int)
    bounds _ = ((0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1))

instance (SingI a, SingI b, SingI c) => Bounds (N a, N b, N c) where
    type Bound (N a, N b, N c) = (Int, Int, Int)
    bounds _ = ((0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1))

instance (SingI a, SingI b, SingI c, SingI d) => Bounds (N a, N b, N c, N d) where
    type Bound (N a, N b, N c, N d) = (Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e) =>
         Bounds (N a, N b, N c, N d, N e) where
    type Bound (N a, N b, N c, N d, N e) = (Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f) =>
         Bounds (N a, N b, N c, N d, N e, N f) where
    type Bound (N a, N b, N c, N d, N e, N f) = (Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g) where
    type Bound (N a, N b, N c, N d, N e, N f, N g) =
        (Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h) =
        (Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h, N i) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h, N i) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1,
                 fromNat (N :: N i) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1,
                 fromNat (N :: N i) - 1,
                 fromNat (N :: N j) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1,
                 fromNat (N :: N i) - 1,
                 fromNat (N :: N j) - 1,
                 fromNat (N :: N k) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k, SingI l) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k,
                 N l) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k, N l) =
        (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1,
                 fromNat (N :: N i) - 1,
                 fromNat (N :: N j) - 1,
                 fromNat (N :: N k) - 1,
                 fromNat (N :: N l) - 1))

instance (SingI a, SingI b, SingI c, SingI d, SingI e, SingI f, SingI g,
          SingI h, SingI i, SingI j, SingI k, SingI l, SingI m) =>
         Bounds (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k, N l,
                 N m) where
    type Bound (N a, N b, N c, N d, N e, N f, N g, N h, N i, N j, N k, N l,
                N m) =
         (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    bounds _ = ((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                (fromNat (N :: N a) - 1,
                 fromNat (N :: N b) - 1,
                 fromNat (N :: N c) - 1,
                 fromNat (N :: N d) - 1,
                 fromNat (N :: N e) - 1,
                 fromNat (N :: N f) - 1,
                 fromNat (N :: N g) - 1,
                 fromNat (N :: N h) - 1,
                 fromNat (N :: N i) - 1,
                 fromNat (N :: N j) - 1,
                 fromNat (N :: N k) - 1,
                 fromNat (N :: N l) - 1,
                 fromNat (N :: N m) - 1))
