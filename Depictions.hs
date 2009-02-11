{-# LANGUAGE ScopedTypeVariables, EmptyDataDecls, TypeSynonymInstances #-}
module Depictions where

-- 2009.02.11
-- Vo Minh Thu
-- This module shows one way to reflect some Haskell types into
-- some Haskell values. The principle is stolen from the LLVM bindings.
-- The most interesting part is how we reflect a function. But
-- there is one glitch : the function has as a special type as
-- a result (here, called R; in LLVM it is IO).

import Foreign.C.Types

-- Type depictions.
data TypeDepiction = TDInt
                   | TDFloat
                   | TDFunction [TypeDepiction] TypeDepiction
  deriving (Eq, Ord, Show)

-- Return type.
data R a = R
give :: a -> R a
give _ = R

class IsType a where
  typeDepiction :: a -> TypeDepiction

class IsType a => IsFunction a where
  functionType :: [TypeDepiction] -> a -> TypeDepiction

class IsType a => IsNotFunction a

instance (IsNotFunction a, IsFunction b) => IsType (a -> b) where
  typeDepiction = functionType []

instance (IsNotFunction a) => IsType (R a) where
  typeDepiction = functionType []

instance (IsNotFunction a) => IsFunction (R a) where
  functionType ts _ = TDFunction (reverse ts) (typeDepiction (undefined :: a))

instance (IsNotFunction a, IsFunction b) => IsFunction (a -> b) where
  functionType ts _ = functionType (typeDepiction (undefined :: a) : ts) (undefined :: b)

instance IsType CInt where
  typeDepiction _ = TDInt

instance IsType CFloat where
  typeDepiction _ = TDFloat

instance IsNotFunction CInt
instance IsNotFunction CFloat

-- Examples.

t0 = typeDepiction (55.0 :: CFloat)
t1 = typeDepiction (\a b -> give $ 1 + a + b :: R CInt)


