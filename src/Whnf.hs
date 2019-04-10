------------------------------------------------------------------------------
--                                                                          --
--  Whnf                                                                    --
--                                                                          --
------------------------------------------------------------------------------

-- This file (when its done) delivers all of the equipment needed to reduce a
-- term to weak-head-normal form.

-- Of course, we need thinning, substitution, pattern matching, etc.

{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards              #-}

module Whnf where

import Data.Bits
import Data.Pair
import Data.Backwards as B
import Data.Foldable

import Control.Monad

import Prelude hiding ((^))
import Syntax

------------------------------------------------------------------------------
-- The type of Reduction systems (stub)
------------------------------------------------------------------------------

data Reduction = Reduction
  deriving Show

------------------------------------------------------------------------------
-- weak-head-normalisation (stub)
------------------------------------------------------------------------------

whnf :: Reduction -> Chk -> Chk
whnf rr (Syn e) = case compute rr e of
  Rad t _ _ -> t
  e -> Syn e
whnf rr t = t

compute :: Reduction -> Syn -> Syn
compute rr e = e -- not really


------------------------------------------------------------------------------
-- Pattern Matching
------------------------------------------------------------------------------

type Stan = (Bwd (String, Poi), Bwd (String, Chk))

match :: Reduction -> Pat -> Chk -> Maybe Stan
match rr = go (-1, -1) where
  go :: Thng -> Pat -> Chk -> Maybe Stan
  go (dh', th') (PMet x (dh, th)) t = do
    t <- (dh .|. dh', th .|. th') ?^ t  -- check dependencies
    return (B0, B0 :< (x, t)) -- return the matching instantiation
  go (dh', _) (PMep x dh) (Poi p) = do
    p <- (dh' .|. dh, -1) ?^ p
    return (B0 :< (x, p), B0)
  go z@(dh', th') p t = case (p, whnf rr t) of  -- structural, up to whnf
    (PCan c ps, Can d ts) | c == d -> fmap fold $ sequence =<< syncWith (go z) ps ts
    (PAbs p,    Abs t)             -> go (dh', shift th' 1) p t
    (PHiD p,    HiD t)             -> go (shift dh' 1, th') p t
    (Pat0,      Poi P0)            -> Just mempty
    (Pat1,      Poi P1)            -> Just mempty
    _ -> Nothing

-- Length mismatch is usually a bug, not a failure, but we're open
-- to overloading, so confuse away!
-- Patterns are assumed to be linear. We must check that in user-given rules.


------------------------------------------------------------------------------
-- Metavariable Instantiation
------------------------------------------------------------------------------

class Inst t where
  (?%) :: t         -- term over Delta
       -> ( Sbsn    -- substitution from Gamma to Delta
          , Stan    -- mapping of metas to terms over Gamma, X
          )
       -> t         -- term over Delta



instance Inst Chk where
  (m :? sb) ?% sbst@(sb', (_, mvs))
    | Just v <- B.lookup m mvs = v % mappend (sb ?% sbst) sb'
    | otherwise = m :? (sb ?% sbst)
  Can c ts  ?% sbst = Can c (ts ?% sbst)
  Abs t     ?% ((ps, es), st) = Abs (t ?% ((ps, susys es), st))
  HiD t     ?% ((ps, es), st) = Abs (t ?% ((supos ps, es), st))
  Syn e     ?% sbst = Syn (e ?% sbst)
  Poi p     ?% sbst = Poi (p ?% sbst)

instance Inst Syn where
  Var i    ?% sbst = Var i
  (e :/ s) ?% sbst = (e ?% sbst) :/ (s ?% sbst)
  Rad t ty ?% sbst = Rad (t ?% sbst) (ty ?% sbst)

instance Inst Poi where
  PM m ps pp ?% sbst@(sb, (mds, _))
    | Just d <- B.lookup m mds =
      scale (d % mappend (ps ?% sbst, B0) sb) (pp ?% sbst)
    | otherwise = PM m (ps ?% sbst) (pp ?% sbst)
  p ?% _ = p

instance Inst x => Inst (Bwd x) where
  xs ?% mvs = fmap (?% mvs) xs

instance (Inst x, Inst y) => Inst (x, y) where
  (x, y) ?% mvs = (x ?% mvs, y ?% mvs)

instance Inst x => Inst (Pair x) where
  pp ?% mvs = fmap (?% mvs) pp

deriving instance Inst x => Inst (Boundary x)

------------------------------------------------------------------------------
-- Simultaneous Substitution
------------------------------------------------------------------------------

class Sbst t where
  (%) :: t -> Sbsn -> t

instance Sbst Chk where
  Can c ts  % sb       = Can c (ts % sb)
  Abs t     % (ps, es) = Abs (t % (ps, wksys es))
  HiD t     % (ps, es) = HiD (t % (wkpos ps, es))
  Syn e     % sb       = Syn (e % sb)
  Poi p     % sb       = Poi (p % sb)
  (m :? ts) % sb       = m :? (ts % sb)

susys :: Bwd Syn -> Bwd Syn
susys es = es ^ (-1, -2)    -- -1 identity on dims; -2 shifts vars
wksys :: Bwd Syn -> Bwd Syn
wksys es = susys es
         :< Var 0           -- top de Bruijn variable

supos :: Bwd Poi -> Bwd Poi
supos ps = ps ^ (-2, -1)    -- -2 shifts dims; -1 identity on vars (so what?)
wkpos :: Bwd Poi -> Bwd Poi
wkpos ps = supos ps
         :< pzero           -- top dimension

instance Sbst Syn where
  Var i    % (_, es) = case B.elemAt i es of
    Nothing -> error "IMPOSSIBLE"
    Just e  -> e
  (e :/ s) % sb      = (e % sb) :/ (s % sb)
  Rad t ty % sb      = Rad (t % sb) (ty % sb)

instance Sbst Poi where
  PM m ps pp % sb = PM m (ps % sb) (pp % sb)
  p % (ps, _) = go p ps where
    go P0      _         = P0
    go P1      _         = P1
    go (PS p)  (ps :< _) = go p ps
    go (PI pp) (ps :< p) = scale p $ fmap (flip go ps) pp

instance Sbst x => Sbst (Bwd x) where
  ts % sb = fmap (% sb) ts

instance (Sbst x, Sbst y) => Sbst (x, y) where
  (x, y) % sb = (x % sb, y % sb)

instance Sbst x => Sbst (Pair x) where
  pp % sb = fmap (% sb) pp

deriving instance Sbst x => Sbst (Boundary x)


------------------------------------------------------------------------------
-- Thinning and Thickening
------------------------------------------------------------------------------

type Thng = (Integer, Integer)


class Thin t where
  (^)  :: t -> Thng -> t
  (?^) :: Thng -> t -> Maybe t
  -- dhth ?^ (t ^ dhth) == Just t

instance Thin Int where -- thinning a de Bruijn index
  n ^ (_, th) = go n th where
    go n th = case (n, shift th (-1), testBit th 0) of
     (n, th, False)  -> go n th + 1
     (0, _ , True)   -> 0
     (n, th, True)   -> go (n - 1) th + 1
  (_, th) ?^ n = go th n where
    go th n = case (shift th (-1), testBit th 0, n) of
     (_,  b, 0)    -> guard b >> Just 0
     (th, b, n)    -> (if b then succ else id) <$> go th (n - 1)

instance Thin Poi where
  PM m ps pp ^ dhth = PM m (ps ^ dhth) (pp ^ dhth)
  p ^ (dh, _) = go p dh where
    go P0 _ = P0
    go P1 _ = P1
    go p dh = case (p, shift dh (-1), testBit dh 0) of
      (p,     dh, False)  -> psuc (go p dh)
      (PS p,  dh, True)   -> psuc (go p dh)
      (PI pp, dh, True)   -> pif0 $ fmap (flip go dh) pp
  dhth ?^ PM m ps pp = PM m <$> (dhth ?^ ps) <*> (dhth ?^ pp)
  (dh, _) ?^ p = go dh p where
    go dh P0 = pure P0
    go dh P1 = pure P1
    go dh p = case (p, shift dh (-1), testBit dh 0) of
      (PI pp, dh, b) -> guard b >> (pif0 <$> traverse (go dh) pp)
      (PS p,  dh, b) -> (if b then psuc else id) <$> go dh p

instance Thin Chk where
  Can c ts  ^ dhth     = Can c (ts ^ dhth)
  Abs t     ^ (dh, th) = Abs (t ^ (dh, wkth th))
  HiD t     ^ (dh, th) = HiD (t ^ (wkth dh, th))
  Syn e     ^ dhth     = Syn (e ^ dhth)
  Poi p     ^ dhth     = Poi (p ^ dhth)
  (m :? ts) ^ dhth     = m :? (ts ^ dhth)
  dhth     ?^ Can c ts  = Can c <$> (dhth ?^ ts)
  (dh, th) ?^ Abs t     = Abs <$> ((dh, wkth th) ?^ t)
  (dh, th) ?^ HiD t     = HiD <$> ((wkth dh, th) ?^ t)
  dhth     ?^ Syn e     = Syn <$> (dhth ?^ e)
  dhth     ?^ Poi p     = Poi <$> (dhth ?^ p)
  dhth     ?^ (m :? ts) = (m :?) <$> (dhth ?^ ts)

wkth :: Integer -> Integer
wkth th = shift th 1 .|. 1

instance Thin Syn where
  Var n    ^ dhth = Var (n ^ dhth)
  (e :/ s) ^ dhth = (e ^ dhth) :/ (s ^ dhth)
  Rad t ty ^ dhth = Rad (t ^ dhth) (ty ^ dhth)
  dhth ?^ Var n    = Var <$> (dhth ?^ n)
  dhth ?^ (e :/ s) = (:/) <$> (dhth ?^ e) <*> (dhth ?^ s)
  dhth ?^ Rad t ty = Rad <$> (dhth ?^ t) <*> (dhth ?^ ty)

instance Thin x => Thin (Bwd x) where
  ts ^ dhth = fmap (^ dhth) ts
  dhth ?^ ts = traverse (dhth ?^) ts

instance (Thin x, Thin y) => Thin (x, y) where
  (x, y) ^ dhth = (x ^ dhth, y ^ dhth)
  dhth ?^ (x, y) = (,) <$> (dhth ?^ x) <*> (dhth ?^ y)

instance Thin x => Thin (Pair x) where
  pp ^ dhth = fmap (^ dhth) pp
  dhth ?^ pp = traverse (dhth ?^) pp

deriving instance Thin x => Thin (Boundary x)
