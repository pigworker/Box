module Whnf where

import Data.Bits
import Control.Monad

import Prelude hiding ((^))
import Syntax

data Reduction = Reduction
  deriving Show

match :: Reduction -> Pat -> Chk -> Maybe [(String, Chk)]
match rr (PMet x dhth) t = (dhth ?^ t) >>= \ t -> Just [(x, t)]
match rr p t = case (p, whnf rr t) of
 (PCan c ps, Can d ts) | c == d -> matches rr ps ts
 (PAbs p,    Abs t)             -> match rr p t
 (PHiD p,    HiD t)             -> match rr p t
 (Pat0,      Poi P0)            -> Just []
 (Pat1,      Poi P1)            -> Just []
 _ -> Nothing

matches :: Reduction -> [Pat] -> [Chk] -> Maybe [(String, Chk)]
matches rr []       []       = Just []
matches rr (p : ps) (t : ts) = (++) <$> match rr p t <*> matches rr ps ts
matches rr _        _        = Nothing

whnf :: Reduction -> Chk -> Chk
whnf rr (Syn e) = case compute rr e of
  Rad t _ _ -> t
  e -> Syn e
whnf rr t = t

compute :: Reduction -> Syn -> Syn
compute rr e = e -- not really

class Sbst t where
  (%) :: t -> ([Poi], [Syn]) -> t

instance Sbst Chk where
  Can c ts % sb = Can c (ts % sb)
  Abs t % (ps, es) = Abs (t % (ps, Var 0 : (es ^ (-1, -2))))
  HiD t % (ps, es) = HiD (t % (PI P0 P1 : (ps ^ (-2, -1)), es))
  Syn e % sb = Syn (e % sb)
  Poi p % sb = Poi (p % sb)
  (m :? ts) % sb = m :? (ts % sb)

instance Sbst Syn where
  Var i % (_, es) = es !! i
  (e :/ s) % sb = (e % sb) :/ (s % sb)
  Rad t ts ty % sb = Rad (t % sb) (ts % sb) (ty % sb)

instance Sbst Poi where
  p % (ps, _) = go p ps where
    go P0 _ = P0
    go P1 _ = P1
    go (PS p) (_ : ps) = go p ps
    go (PI p0 p1) (p : ps) = scale p (go p0 ps, go p1 ps)

instance Sbst x => Sbst [x] where
  ts % sb = fmap (% sb) ts

instance (Sbst x, Sbst y) => Sbst (x, y) where
  (x, y) % sb = (x % sb, y % sb)

class Thin t where
  (^) :: t -> (Integer, Integer) -> t
  (?^) :: (Integer, Integer) -> t -> Maybe t

instance Thin Int where
  n ^ (_, th) = go n th where
    go n th = case (n, shift th (-1), testBit th 0) of
     (n, th, False)  -> go n th + 1
     (0, _ , True)   -> 0
     (n, th, True)   -> go (n - 1) th + 1
  (_, th) ?^ n = go th n where
    go n th = case (n, shift th (-1), testBit th 0) of
     (0, _, b)     -> guard b >> Just 0
     (n, th, b)    -> (if b then succ else id) <$> go (n - 1) th

instance Thin Poi where
  p ^ (dh, _) = go p dh where
    go P0 _ = P0
    go P1 _ = P1
    go p dh = case (p, shift dh (-1), testBit dh 0) of
      (p,        dh, False)  -> psuc (go p dh)
      (PS p,     dh, True)   -> psuc (go p dh)
      (PI p0 p1, dh, True)   -> pif0 (go p0 dh) (go p1 dh)
  (dh, _) ?^ p = go dh p where
    go dh P0 = pure P0
    go dh P1 = pure P1
    go dh p = case (p, shift dh (-1), testBit dh 0) of
      (PI p0 p1, dh, b) -> guard b >> (pif0 <$> go dh p0 <*> go dh p1)
      (PS p, dh, b) -> (if b then psuc else id) <$> go dh p

wk :: Integer -> Integer
wk th = shift th 1 .|. 1

instance Thin Chk where
  Can c ts ^ dhth = Can c (ts ^ dhth)
  Abs t ^ (dh, th) = Abs (t ^ (dh, wk th))
  HiD t ^ (dh, th) = HiD (t ^ (wk dh, th))
  Syn e ^ dhth = Syn (e ^ dhth)
  Poi p ^ dhth = Poi (p ^ dhth)
  (m :? ts) ^ dhth = m :? (ts ^ dhth)
  dhth ?^ Can c ts = Can c <$> (dhth ?^ ts)
  (dh, th) ?^ Abs t = Abs <$> ((dh, wk th) ?^ t)
  (dh, th) ?^ HiD t = HiD <$> ((wk dh, th) ?^ t)
  dhth ?^ Syn e = Syn <$> (dhth ?^ e)
  dhth ?^ Poi p = Poi <$> (dhth ?^ p)
  dhth ?^ (m :? ts) = (m :?) <$> (dhth ?^ ts)

instance Thin Syn where
  Var n ^ dhth = Var (n ^ dhth)
  (e :/ s) ^ dhth = (e ^ dhth) :/ (s ^ dhth)
  Rad t ts ty ^ dhth = Rad (t ^ dhth) (ts ^ dhth) (ty ^ dhth)
  dhth ?^ Var n = Var <$> (dhth ?^ n)
  dhth ?^ (e :/ s) = (:/) <$> (dhth ?^ e) <*> (dhth ?^ s)
  dhth ?^ Rad t ts ty = Rad <$> (dhth ?^ t) <*> (dhth ?^ ts) <*> (dhth ?^ ty)

instance Thin x => Thin [x] where
  ts ^ dhth = fmap (^ dhth) ts
  dhth ?^ ts = traverse (dhth ?^) ts

instance (Thin x, Thin y) => Thin (x, y) where
  (x, y) ^ dhth = (x ^ dhth, y ^ dhth)
  dhth ?^ (x, y) = (,) <$> (dhth ?^ x) <*> (dhth ?^ y)
