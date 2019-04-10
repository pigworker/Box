------------------------------------------------------------------------------
--                                                                          --
-- Backwards lists                                                          --
--                                                                          --
------------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.Backwards where

data Bwd a = B0 | Bwd a :< a
  deriving (Show, Eq, Functor, Foldable, Traversable)

fromList :: [a] -> Bwd a
fromList = foldr (flip (:<)) B0

instance Semigroup (Bwd a) where
  xs <> ys = case ys of
    B0      -> xs
    zs :< z -> (xs <> zs) :< z

instance Monoid (Bwd a) where
  mempty = B0

instance Applicative Bwd where
  pure a = B0 :< a
  B0 <*> xs = B0
  fs <*> B0 = B0
  (fs :< f) <*> (xs :< x) = (fs <*> xs) :< f x

iterate :: (a -> a) -> a -> Bwd a
iterate f = go where go x = go (f x) :< x

lookup :: Eq a => a -> Bwd (a, b) -> Maybe b
lookup x = foldr (\ (y, b) acc -> if x == y then Just b else acc) Nothing

elemAt :: Int -> Bwd a -> Maybe a
elemAt _ B0        = Nothing
elemAt 0 (xs :< x) = Just x
elemAt n (xs :< x) = elemAt (n-1) xs

syncWith :: (a -> b -> c) -> Bwd a -> Bwd b -> Maybe (Bwd c)
syncWith f B0        B0        = Just B0
syncWith f (as :< a) (bs :< b) = (:< f a b) <$> syncWith f as bs
syncWith f _ _ = Nothing
