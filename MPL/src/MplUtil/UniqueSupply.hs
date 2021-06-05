{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-cse #-}
module MplUtil.UniqueSupply where

import Optics
import Optics.State.Operators

import System.IO.Unsafe
import Data.IORef
import Control.Arrow
import Data.Word

import MplUtil.Data.Stream (Stream (..))
import qualified MplUtil.Data.Stream as Stream

import Control.Monad.State

import Debug.Trace
import Data.Ix


{- Module for defining a lazy tree of unique values..
 -
 - Some may think this is unneccassary because unique values
 - can just be generated by incrementing a counter in the state monad.
 - So, we briefly discuss the motivation for this machinery's existance..
 - Let's say we have some code here in a state monad with a counter for
 - unique values:
 - do
 -      res <- someBottomValue
 -      uniqueValueCounter <- get 
 -      let nres = someComputationThatNeedsAUniqueValue uniqueValueCounter
 -      return nres
 - The problem with this is, is that in order to evaluate `someComputationThatNeedsAUniqueValue`
 - we need to first evaluate the counter after `someBottomValue` but in doing so, we will
 - accidentally evaluate a bottom value too early and the program will crash. With a unique supply,
 - we can instead write
 - do
 -      uniqsup <- freshUniqueSupply
 -      res <- someBottomValue
 -      let nres = someComputationThatNeedsAUniqueValue uniqsup
 -      return nres
 - So, if we never use other parts of the state, then this will gracefully just return nres
 - without ever needing to evaluate the bottom value to get whatever unique value should be
 - fed to `someComputationThatNeedsAUniqueValue`
 -}

-- | The lazy tree of unique values..
data UniqueSupply = 
    UniqueSupply !Word UniqueSupply UniqueSupply
$(makeClassy ''UniqueSupply)

-- | Wrapper for a Word that is unique.
newtype Unique = Unique Word
  deriving (Show, Eq, Ord, Ix, Read, Enum)

-- | Gets the unique value from a given unique supply.
uniqueFromSupply :: UniqueSupply -> Unique 
uniqueFromSupply ~(UniqueSupply a _ _) = Unique a

-- | Generates infinite fresh uniques.
uniquesFromSupply :: 
    UniqueSupply -> 
    Stream Unique
uniquesFromSupply supply = 
    uniqueFromSupply supply 
        :/ uniquesFromSupply r
  where
    ~(_,r) = split supply

-- | Generates infinite fresh unique supplies.
uniqueSupplies :: 
    UniqueSupply -> 
    [UniqueSupply]
uniqueSupplies supply = l : uniqueSupplies r
  where
    ~(l,r) = split supply

-- | Initializses a fresh unique supply given a seed Word
initUniqueSupply :: Word -> IO UniqueSupply
initUniqueSupply seed = initUniqueSupply' =<< newIORef seed

-- | Main driver function for initializing a unique supply
-- the magic is in the unsafeInterleaveIO call which ensures
-- that we can get a lazy tree of unique values ( but mind you
-- the actual values are non determanistic.
initUniqueSupply' :: IORef Word -> IO UniqueSupply
initUniqueSupply' ref = unsafeInterleaveIO $ do
    n <- freshWord ref
    l <- initUniqueSupply' ref
    r <- initUniqueSupply' ref
    return (UniqueSupply n l r)

{-
{-# NOINLINE uniqueIntRef #-}
uniqueIntRef :: IORef Int
uniqueIntRef = unsafePerformIO $ newIORef 0
-}

-- | increments the word
freshWord :: IORef Word -> IO Word
freshWord ref = atomicModifyIORef' ref (succ&&&id) 
    

-- | Splits a unique supply to give 2 new unique supplies.
split :: UniqueSupply -> (UniqueSupply, UniqueSupply)
split ~(UniqueSupply _ l r)= (l, r)


instance Show UniqueSupply where
    show (UniqueSupply n _ _) = "UniqueSupply " ++ show n

{-
instance Show Unique where
    show (Unique n) = show n
    -}

-- | Generates a fresh unique supply for the user
-- remark -- a bit inefficient with the unique supply here!
freshUniqueSupply ::
    ( MonadState c m
    , HasUniqueSupply c ) => 
    m UniqueSupply
freshUniqueSupply =
    uniqueSupply %%= split

-- | TODO deprecate this... It does not ``split" a unique supply...
-- running the next computation in the state monad will still depend on
-- the values before this one...
splitUniqueSupply ::
    ( MonadState c m
    , HasUniqueSupply c ) => 
    m a -> m a
splitUniqueSupply action = do
    uniqsupply <- freshUniqueSupply
    res <- action
    uniqueSupply .= uniqsupply
    return res
