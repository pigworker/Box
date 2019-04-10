------------------------------------------------------------------------------
--                                                                          --
-- Homogeneous Pairs                                                        --
--                                                                          --
------------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.Pair where

data Pair a = P
  { proj0 :: a
  , proj1 :: a
  }
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative Pair where
  pure a = P a a
  P f g <*> P x y = P (f x) (g y)
