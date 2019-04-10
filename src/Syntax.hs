------------------------------------------------------------------------------
--                                                                          --
--  Syntax                                                                  --
--                                                                          --
------------------------------------------------------------------------------

-- This file gives the lexical structure, raw unscoped syntax
-- and de Bruijn syntaxes for terms in our calculus.

-- The syntax is not remotely sophisticated.

{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternGuards     #-}

module Syntax where

import Prelude hiding (lex)
import Data.Char
import Data.List
import Data.Either
import Data.Backwards as B
import Data.Pair
import Data.Traversable
import Control.Applicative
import Control.Arrow
import Control.Monad

------------------------------------------------------------------------------
-- Lexical Structure
------------------------------------------------------------------------------

data Tok
  = TokI String            -- identifiers (alphanumeric)
  | TokS String            -- symbols
  | TokO Brk String        -- open brackets (including punctuation), e.g., [-
  | TokC String Brk        -- close brackets (including punctuation), e.g, -]
  deriving (Show, Eq)

-- the varieties of bracket
data Brk = Round | Square | Curly deriving (Show, Eq)

solo :: String -- these are only ever tokens by themselves
solo = ",;?!"

 -- detect chars which may occur consecutively in symbol tokens
isSym :: Char -> Bool
isSym c =
  not (isSpace c) &&
  not (isAlphaNum c) &&
  not (elem c "({[)]}") &&
  not (elem c solo)

-- detect open brackets
getOpen :: Char -> Maybe Brk
getOpen '(' = Just Round
getOpen '[' = Just Square
getOpen '{' = Just Curly
getOpen _ = Nothing

-- detect close brackets
getClose :: Char -> Maybe Brk
getClose ')' = Just Round
getClose ']' = Just Square
getClose '}' = Just Curly
getClose _ = Nothing

-- tokenise a string
lex :: String -> [Tok]
lex "" = []
lex cs@(c : s)
  | elem c solo            -- a symbol on its own
  = TokS [c] : lex s
  | isSpace c              -- skip over whitespace
  = lex s
  | isAlphaNum c           -- the start of an identifier
  = case span isAlphaNum s of
    (t, u) -> TokI (c : t) : lex u
  | Just b <- getOpen c    -- the start of an open bracket
  = case span isSym s of
    (t, d : u) | Just b' <- getClose d
      -> let l = length t
             t0 = take ((l + 1) `div` 2) t
             t1 = drop (l `div` 2) t
         in  TokO b t0 : TokC t1 b' : lex u
         -- so [--] gives [- -]
         -- and [-] also gives [- -]
    (t, u) -> TokO b t : lex u
  | otherwise              -- it must be a symbolic token
  = case span isSym cs of
    (t, d : u) | Just b <- getClose d -> TokC t b : lex u
    (t, u) -> TokS t : lex u


------------------------------------------------------------------------------
-- Parser Combibnators (bargain basement)
------------------------------------------------------------------------------

newtype Parse x = Parse {parse :: [Tok] -> Maybe (x, [Tok])}
-- look ma, no monad!
instance Applicative Parse where
  pure x = Parse $ \ ts -> Just (x, ts)
  Parse f <*> Parse s = Parse $ \ ts0 -> do
    (f', ts1) <- f ts0
    (s', ts2) <- s ts1
    return (f' s', ts2)
instance Alternative Parse where
  empty = Parse $ \ _ -> Nothing
  Parse a <|> Parse b = Parse $ \ ts -> case a ts of
    Nothing -> b ts
    z -> z
instance Functor Parse where fmap = (<*>).pure

eat :: (Tok -> Maybe a) -> Parse a
eat f = Parse $ \ ts -> case ts of
  t : us | Just a <- f t -> Just (a, us)
  _ -> Nothing

tok :: Tok -> Tok -> Maybe ()  -- use like (eat (tok (TokS x)))
tok a b = guard (a == b)

punc :: String -> Parse ()
punc x = eat (tok (TokS x))

between :: Tok -> Tok -> Parse a -> Parse a
between topen tclose p = eat (tok topen) *> p <* eat (tok tclose)

parens :: Brk -> Parse a -> Parse a
parens brk = between (TokO brk "") (TokC "" brk)

nom :: Tok -> Maybe String     -- use like (eat nom)
nom (TokI x) = Just x
nom _ = Nothing

sep :: Tok -> Parse a -> Parse [a]  -- sep s p gets p1 s p2 s ... s ... pn
sep s p = (:) <$> p <*> more
      <|> pure []
  where
    more = (:) <$ eat (tok s) <*> p <*> more
       <|> pure []

------------------------------------------------------------------------------
-- Raw unscoped syntax
------------------------------------------------------------------------------

newtype Boundary a = B { outB :: Bwd (Pair a) }
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Raw
  = RA String                     -- atoms
  | Raw :! Boundary Raw           -- r[r10-r11,...,rn0-rn1]  -- nonempty
  | Raw :$ [Raw]                  -- r r1 ... rn    (n >= 1)
  | String :. Raw                 -- x.r  (value abstraction)
  | String :- Raw                 -- x|r  (dimension abstraction)
  | RadR Raw (Boundary Raw) Raw   -- r : [r10-r11,...,rn0-rn1] R
  | MetR String [String]          -- ?m-x1...-xn  (metavars excluding dependency)
  | MepR String [String]          -- !m-i1-...-ik (metadimensions ditto)
  deriving Show

exterior :: Parse (Boundary Raw)     -- exterior of n-dimensional thing
exterior = parens Square
         $ B . fromList <$> sep (TokS ",") (P <$> raw <* punc "-" <*> raw)

-- The recurring pattern is to write helper functions being
-- (i)  a smart constructor which assembles a term from a prefix and a suffix
-- (ii) a parser for valid suffices
-- and then make the main function use (i) applicatively.

raw :: Parse Raw               -- anything but a radical
raw = app <$> wee <*> many wee where
  app :: Raw -> [Raw] -> Raw     -- smart constructor preventing empty apps
  app t [] = t
  app t ts = t :$ ts

huge :: Parse Raw              -- anything, including radicals
huge = rad <$> raw <*> radex where
  rad :: Raw -> Maybe (Boundary Raw, Raw) -> Raw  -- radical smart constructor
  rad t (Just (ts, ty)) = RadR t ts ty
  rad t Nothing = t
  radex :: Parse (Maybe (Boundary Raw, Raw))  -- radicals, rightward from colon
  radex =  Just <$ punc ":" <*> ((,) <$> (exterior <|> pure (B B0)) <*> raw)
       <|> pure Nothing -- it turns out it wasn't a radical, after all

wee :: Parse Raw
wee = flip ($) <$> atom <*> (flip (:!) <$> exterior <|> pure id)

atom :: Parse Raw  -- things which don't need parentheses
atom = parens Round huge
   <|> flip ($) <$> eat nom <*> bind
   <|> meta <*> eat nom <*> many (id <$ punc "-" <*> eat nom)
  where
  bind :: Parse (String -> Raw)
  bind = flip <$> ((:.) <$ punc "." <|> (:-) <$ punc "|") <*> raw
     <|> pure RA

  meta :: Parse (String -> [String] -> Raw)
  meta = MetR <$ punc "?" <|> MepR <$ punc "!"

------------------------------------------------------------------------------
-- Points and their smart constructors
------------------------------------------------------------------------------

data Poi           -- points in normal form
  = P0 | P1        -- endpoints
  | PS Poi         -- weakening (no dependence on most local dimension)
  | PI (Pair Poi)  -- conditional on most local dimension, not in cases' scope
  | PM String (Bwd Poi) (Pair Poi)  -- metavariable usage
  deriving (Show, Eq)

-- What is going on with points and metadimensions?
-- PM must never occur inside PI or PS.

-- top variable: branch over endpoints
pzero :: Poi
pzero = PI (P P0 P1)

-- smart constructor ensuring we never weaken an endpoint
psuc :: Poi -> Poi
psuc P0     = P0
psuc P1     = P1
psuc p      = PS p

-- smart constructor ensuring conditionals actually matter
pif0 :: Pair Poi -> Poi
pif0 (P p0 p1) | p0 == p1  = psuc p0  -- no choice, weaken instead
pif0 pp                    = PI pp

-- rescaling p[p0-p1] where each is normal, restoring normality
scale :: Poi -> Pair Poi -> Poi
scale _ (P p0 p1) | p0 == p1 = p0
scale (PM m ps (P m0 m1)) pp = PM m ps $ P (scale m0 pp) (scale m1 pp)
scale P0 (P p0 p1) = p0
scale P1 (P p0 p1) = p1
scale (PS p) (P (PS p0) (PS p1))  -- definitely no dependency on most local
  = psuc (scale p (P p0 p1))      -- so weaken
scale p (P p0 p1)  -- definitely some dependency on most local
  = pif0 $ P       -- so branch on most local
      (branch pr0) -- specialise to most local 0
      (branch pr1) -- specialise to most local 1
  where
  -- branch specialises scale to most local's projection
  branch prj = scale (prj p) (P (prj p0) (prj p1))
  pr0 = pr proj0; pr1 = pr proj1
  -- pr specialises most local to a projection
  pr f (PS p)  = p    -- no dependency
  pr f (PI pp) = f pp -- choose f branch
  pr f p       = p    -- endpoint


------------------------------------------------------------------------------
-- de Bruijn Refineries
------------------------------------------------------------------------------

-- General equipment

type Scope = ( Bwd String  -- names of dimensions [local,..,global]
             , Bwd String  -- names of variables  [local,..,global]
             )

mkThin :: Bwd String  -- scope
       -> [String]    -- excluded names
       -> Integer     -- bitwise selection
mkThin scp excluded = foldr step 0 scp where
  step :: String -> Integer -> Integer
  step x i
    | x `elem` excluded = 2 * i     -- excluded, emit 0
    | otherwise         = 2 * i + 1 -- included, emit 1

type Sbsn = (Bwd Poi, Bwd Syn)

-- Infinite id point substitution
poid :: Bwd Poi
poid = B.iterate PS pzero

-- Infinite synthesizable substitution
syid :: Bwd Syn
syid = Var <$> fromList [0..]

-- Finite substitution, matching the size of a given scope
idSb :: Scope -> Sbsn
idSb (is, xs) =
  ( poid <* is
  , syid <* xs
  )

can :: (Raw -> Maybe x) -> Raw -> Maybe (String, Bwd x)
can f (RA c)    = pure (c, B0)
can f (r :$ rs) = (\ (c, ts) us -> (c, mappend ts $ fromList us))
              <$> can f r <*> traverse f rs
can _ _ = Nothing


-- Patterns

data Pat
  = PCan String (Bwd Pat)           -- canonical
  | PAbs Pat                        -- variable abstraction
  | PHiD Pat                        -- dimension abstraction
  | Pat0                            -- point 0
  | Pat1                            -- point 1
  | PMet String    -- metavariable binding site
         ( Integer -- dimension bitwise selection
         , Integer -- variable bitwise selection
         )
  | PMep String Integer  -- metadimension binding site
  deriving Show

pat :: Scope -> Raw -> Maybe Pat
pat (is, xs) (MetR m us) = pure (PMet m (mkThin is us, mkThin xs us))
pat (is, _)  (MepR m us) = pure (PMep m (mkThin is us))
pat (is, xs) (x :. r) = PAbs <$> pat (is, xs :< x) r
pat (is, xs) (i :- r) = PHiD <$> pat (is :< i, xs) r
pat _ (RA "0") = pure Pat0
pat _ (RA "1") = pure Pat1
pat g r = uncurry PCan <$> can (pat g) r

-- Checkable terms

data Chk
  = Can String (Bwd Chk) -- canonical
  | Abs Chk              -- variable abstraction
  | HiD Chk              -- dimension abstraction
  | Syn Syn              -- synthesizable
  | Poi Poi              -- point
  | String :? Sbsn       -- metavariable use site, with substitution
  deriving Show

chk :: Scope -> Raw -> Maybe Chk
chk (is, xs) (x :. r) = Abs <$> chk (is, xs :< x) r
chk (is, xs) (i :- r) = HiD <$> chk (is :< i, xs) r
chk g (MetR x _) = pure (x :? idSb g)
chk g (MetR x _ :$ rs) = ((x :?) . (fromList *** fromList) . partitionEithers)
                     <$> traverse stan rs
  where
  stan :: Raw -> Maybe (Either Poi Syn)
  stan r = Left  <$> poi g r
       <|> Right <$> syn g r
chk g r = Poi <$> poi g r
      <|> Syn <$> syn g r
      <|> uncurry Can <$> can (chk g) r


-- Synthesizable terms

data Syn
  = Var !Int                   -- de Bruijn variable
  | Syn :/ Chk                 -- elim form
  | Rad Chk (Boundary Chk) Chk -- radical
  deriving Show

syn :: Scope -> Raw -> Maybe Syn
syn (_, xs) (RA x) = Var <$> foldr checkVar Nothing xs where
  checkVar here there | x == here = Just 0
                      | otherwise = (1+) <$> there
syn g (RadR t ts ty) = Rad <$> chk g t <*> traverse (chk g) ts <*> chk g ty
syn g (r :$ rs) = foldl (:/) <$> syn g r <*> traverse (chk g) rs
syn _ _ = Nothing


-- Points

poi :: Scope -> Raw -> Maybe Poi
poi _ (RA "0") = Just P0
poi _ (RA "1") = Just P1
poi g@(is, _) (RA i) = foldr checkVar Nothing is where
  checkVar here there
     | i == here = Just pzero
     | otherwise = psuc <$> there
poi g (MepR m []) = pure (PM m B0 (P P0 P1))
poi g (MepR m [] :$ rs) =
  PM m <$> traverse (poi g) (fromList rs) <*> pure (P P0 P1)
poi g (r :! rrs) = foldl scale <$> poi g r <*> (outB <$> traverse (poi g) rrs)
poi _ _ = Nothing

------------------------------------------------------------------------------
-- for testing in the repl
------------------------------------------------------------------------------

chkMe :: Scope -> String -> Maybe Chk
chkMe g s = do
  (r, []) <- parse raw (lex s)
  chk g r

patMe :: Scope -> String -> Maybe Pat
patMe g s = do
  (r, []) <- parse raw (lex s)
  pat g r
