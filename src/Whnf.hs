------------------------------------------------------------------------------
--                                                                          --
--  Whnf                                                                    --
--                                                                          --
------------------------------------------------------------------------------

-- This file (when its done) delivers all of the equipment needed to reduce a
-- term to weak-head-normal form.

-- Of course, we need thinning, substitution, pattern matching, etc.


{-# LANGUAGE PatternGuards #-}
module Whnf where

import Data.Bits
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

type Stan = ([(String, Poi)], [(String, Chk)])

match :: Reduction -> Pat -> Chk -> Maybe Stan
match rr = go (-1, -1) where
  go (dh', th') (PMet x (dh, th)) t = do
    t <- (dh .|. dh', th .|. th') ?^ t  -- check dependencies
    return ([], [(x, t)]) -- return the matching instantiation
  go (dh', _) (PMep x dh) (Poi p) = do
    p <- (dh' .|. dh, -1) ?^ p
    return ([(x, p)], [])
  go z@(dh', th') p t = case (p, whnf rr t) of  -- structural, up to whnf
    (PCan c ps, Can d ts) | c == d -> goes ps ts
    (PAbs p,    Abs t)             -> go (dh', shift th' 1) p t
    (PHiD p,    HiD t)             -> go (shift dh' 1, th') p t
    (Pat0,      Poi P0)            -> Just mempty
    (Pat1,      Poi P1)            -> Just mempty
    _ -> Nothing
    where
    goes []       []       = Just mempty
    goes (p : ps) (t : ts) = mappend <$> go z p t <*> goes ps ts
    goes _        _        = Nothing

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
    | Just v <- lookup m mvs = v % mappend (sb ?% sbst) sb'
    | otherwise = m :? (sb ?% sbst)
  Can c ts  ?% sbst = Can c (ts ?% sbst)
  Abs t     ?% ((ps, es), st) = Abs (t ?% ((ps, susys es), st))
  HiD t     ?% ((ps, es), st) = Abs (t ?% ((supos ps, es), st))
  Syn e     ?% sbst = Syn (e ?% sbst)
  Poi p     ?% sbst = Poi (p ?% sbst)

instance Inst Syn where
  Var i       ?% sbst = Var i
  (e :/ s)    ?% sbst = (e ?% sbst) :/ (s ?% sbst)
  Rad t ts ty ?% sbst = Rad (t ?% sbst) (ts ?% sbst) (ty ?% sbst)

instance Inst Poi where
  PM m ps pp ?% sbst@(sb, (mds, _))
    | Just d <- lookup m mds =
      scale (d % mappend (ps ?% sbst, []) sb) (pp ?% sbst)
    | otherwise = PM m (ps ?% sbst) (pp ?% sbst)
  p ?% _ = p

instance Inst x => Inst [x] where
  xs ?% mvs = fmap (?% mvs) xs

instance (Inst x, Inst y) => Inst (x, y) where
  (x, y) ?% mvs = (x ?% mvs, y ?% mvs)


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

susys :: [Syn] -> [Syn]
susys es = es ^ (-1, -2)    -- -1 identity on dims; -2 shifts vars
wksys :: [Syn] -> [Syn]
wksys es = Var 0            -- top de Bruijn variable
         : susys es 

supos :: [Poi] -> [Poi]
supos ps = ps ^ (-2, -1)    -- -2 shifts dims; -1 identity on vars (so what?)
wkpos :: [Poi] -> [Poi]
wkpos ps = pzero            -- top dimension
         : supos ps

instance Sbst Syn where
  Var i       % (_, es) = es !! i
  (e :/ s)    % sb      = (e % sb) :/ (s % sb)
  Rad t ts ty % sb      = Rad (t % sb) (ts % sb) (ty % sb)

instance Sbst Poi where
  PM m ps pp % sb = PM m (ps % sb) (pp % sb)
  p % (ps, _) = go p ps where
    go P0 _                   = P0
    go P1 _                   = P1
    go (PS p) (_ : ps)        = go p ps
    go (PI (p0, p1)) (p : ps) = scale p (go p0 ps, go p1 ps)

instance Sbst x => Sbst [x] where
  ts % sb = fmap (% sb) ts

instance (Sbst x, Sbst y) => Sbst (x, y) where
  (x, y) % sb = (x % sb, y % sb)


------------------------------------------------------------------------------
-- Thinning and Thickening
------------------------------------------------------------------------------

class Thin t where
  (^)  :: t -> (Integer, Integer) -> t
  (?^) :: (Integer, Integer) -> t -> Maybe t
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
      (p,           dh, False)  -> psuc (go p dh)
      (PS p,        dh, True)   -> psuc (go p dh)
      (PI (p0, p1), dh, True)   -> pif0 (go p0 dh, go p1 dh)
  dhth ?^ PM m ps pp = PM m <$> (dhth ?^ ps) <*> (dhth ?^ pp)
  (dh, _) ?^ p = go dh p where
    go dh P0 = pure P0
    go dh P1 = pure P1
    go dh p = case (p, shift dh (-1), testBit dh 0) of
      (PI (p0, p1), dh, b) -> guard b >> (pif0 <$> ((,) <$> go dh p0 <*> go dh p1))
      (PS p,        dh, b) -> (if b then psuc else id) <$> go dh p

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
  Var n       ^ dhth = Var (n ^ dhth)
  (e :/ s)    ^ dhth = (e ^ dhth) :/ (s ^ dhth)
  Rad t ts ty ^ dhth = Rad (t ^ dhth) (ts ^ dhth) (ty ^ dhth)
  dhth ?^ Var n       = Var <$> (dhth ?^ n)
  dhth ?^ (e :/ s)    = (:/) <$> (dhth ?^ e) <*> (dhth ?^ s)
  dhth ?^ Rad t ts ty = Rad <$> (dhth ?^ t) <*> (dhth ?^ ts) <*> (dhth ?^ ty)

instance Thin x => Thin [x] where
  ts ^ dhth = fmap (^ dhth) ts
  dhth ?^ ts = traverse (dhth ?^) ts

instance (Thin x, Thin y) => Thin (x, y) where
  (x, y) ^ dhth = (x ^ dhth, y ^ dhth)
  dhth ?^ (x, y) = (,) <$> (dhth ?^ x) <*> (dhth ?^ y)
