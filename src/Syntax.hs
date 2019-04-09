------------------------------------------------------------------------------
--                                                                          --
--  Syntax                                                                  --
--                                                                          --
------------------------------------------------------------------------------

-- This file gives the lexical structure, raw unscoped syntax
-- and de Bruijn syntaxes for terms in our calculus.

-- The syntax is not remotely sophisticated.


{-# LANGUAGE PatternGuards #-}

module Syntax where

import Prelude hiding (lex)
import Data.Char
import Data.List
import Control.Applicative
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
solo = ",;?"

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

data Raw
  = String :! [(Raw,Raw)]      -- foo[r10-r11,...,rn0-rn1]
  | Raw :$ [Raw]               -- r r1 ... rn    (n >= 1)
  | String :. Raw              -- x.r  (value abstraction)
  | String :- Raw              -- x|r  (dimension abstraction)
  | RadR Raw [(Raw,Raw)] Raw   -- r : [r10-r11,...,rn0-rn1] R
  | MetR String [String]       -- ?m-x1...-xn  (metavars excluding dependency)
  deriving Show

extn :: Parse [(Raw, Raw)]     -- exterior of n-dimensional thing
extn = id <$ eat (tok (TokO Square "")) <*>
  sep (TokS ",") ((,) <$> raw <* eat (tok (TokS "-")) <*> raw) <*
  eat (tok (TokC "" Square))
  <|> pure []

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
  rad :: Raw -> Maybe ([(Raw,Raw)], Raw) -> Raw  -- radical smart constructor
  rad t (Just (ts, ty)) = RadR t ts ty
  rad t Nothing = t
  radex :: Parse (Maybe ([(Raw,Raw)], Raw))  -- radicals, rightward from colon
  radex =  Just <$ eat (tok (TokS ":")) <*> ((,) <$> extn <*> raw)
       <|> pure Nothing -- it turns out it wasn't a radical, after all

wee :: Parse Raw  -- things which don't need parentheses
wee = id <$ eat (tok (TokO Round "")) <*> huge <* eat (tok (TokC "" Round))
  <|> glom <$> eat nom <*> suff
  <|> MetR <$ eat (tok (TokS "?")) <*> eat nom <*>
       many (id <$ eat (tok (TokS "-")) <*> eat nom)
  where
  glom :: String  -- identifier
       -> Either  -- what comes after an identifier?
            (Bool, Raw)  -- a binder (. or |) and its scope?
            [(Raw, Raw)] -- a bunch of scalings/boundaries
       -> Raw     -- smart constructor   
  glom x (Left (True, t))  = x :. t
  glom x (Left (False, t)) = x :- t
  glom x (Right ts) = x :! ts
  suff :: Parse (Either (Bool, Raw) [(Raw, Raw)])
  suff =  Left <$> ((,) <$>
             (True <$ eat (tok (TokS ".")) <|> False <$ eat (tok (TokS "|")))
              <*> raw)
     <|>  Right <$> extn


------------------------------------------------------------------------------
-- Points and their smart constructors
------------------------------------------------------------------------------

data Poi        -- points in normal form
  = P0 | P1     -- endpoints
  | PS Poi      -- weakening (no dependence on most local dimension)
  | PI Poi Poi  -- conditional on most local dimension; cases in shorter scope
  deriving (Show, Eq)

-- smart constructor ensuring we never weaken an endpoint
psuc :: Poi -> Poi
psuc P0 = P0
psuc P1 = P1
psuc p = PS p

-- smart constructor ensuring conditionals actually matter
pif0 :: Poi -> Poi -> Poi
pif0 p0 p1 | p0 == p1  = psuc p0  -- no choice, weaken instead
           | otherwise = PI p0 p1

-- rescaling p[p0-p1] where each is normal, restoring normality
scale :: Poi -> (Poi, Poi) -> Poi
scale P0 (p0, p1) = p0
scale P1 (p0, p1) = p1
scale _ (p0, p1) | p0 == p1 = p0
scale (PS p) (PS p0, PS p1)  -- definitely no dependency on most local
  = psuc (scale p (p0, p1))  -- so weaken
scale p (p0, p1)             -- definitely some dependency on most local
  = pif0  -- so branch on most local
      (scale (pr0 p) (pr0 p0, pr0 p1)) -- specialise to most local 0
      (scale (pr1 p) (pr1 p0, pr1 p1)) -- specialise to most local 1
  where
  -- pr0 specialises most local to 0
  pr0 (PS p)   = p -- no dependency
  pr0 (PI p _) = p -- choose 0 branch
  pr0 p        = p -- endpoint
  -- pr1 specialises most local to 1
  pr1 (PS p)   = p -- no dependency
  pr1 (PI _ p) = p -- choose 1 branch
  pr1 p        = p -- endpoint


------------------------------------------------------------------------------
-- de Bruijn Refineries
------------------------------------------------------------------------------

-- General equipment

type Scope = ( [String]  -- names of dimensions [local,..,global]
             , [String]  -- names of variables  [local,..,global]
             ) -- yuk; should use backward lists

mkThin :: [String]  -- scope
       -> [String]  -- excluded names
       -> Integer   -- bitwise selection
mkThin [] _ = 0
mkThin (x : xs) ys | elem x ys = 2 * mkThin xs ys     -- excluded, emit 0
                   | otherwise = 2 * mkThin xs ys + 1 -- included, emit 1


-- Patterns

data Pat
  = PCan String [Pat]               -- canonical
  | PAbs Pat                        -- variable abstraction
  | PHiD Pat                        -- dimension abstraction
  | Pat0                            -- point 0
  | Pat1                            -- point 1
  | PMet String    -- metavariable binding site
         ( Integer -- dimension bitwise selection
         , Integer -- variable bitwise selection
         )
  deriving Show

pat :: Scope -> Raw -> Maybe Pat
pat (is, xs) (MetR m us) = pure (PMet m (mkThin is us, mkThin xs us))
pat (is, xs) (x :. r) = PAbs <$> pat (is, x : xs) r
pat (is, xs) (i :- r) = PHiD <$> pat (i : is, xs) r
pat g (c :! []) = pure (PCan c [])
pat g ((c :! []) :$ rs) = PCan c <$> traverse (pat g) rs


-- Checkable terms

data Chk
  = Can String [Chk]   -- canonical
  | Abs Chk            -- variable abstraction
  | HiD Chk            -- dimension abstraction
  | Syn Syn            -- synthesizable
  | Poi Poi            -- point
  | String :? [Chk]    -- metavariable use site, with substitution
  deriving Show

chk :: Scope -> Raw -> Maybe Chk
chk (is, xs) (x :. r) = Abs <$> chk (is, x : xs) r
chk (is, xs) (i :- r) = HiD <$> chk (i : is, xs) r
chk g (MetR x _) = pure (x :? [])
chk g (MetR x _ :$ rs) = (x :?) <$> traverse (chk g) rs
chk g r = Poi <$> poi g r
      <|> Syn <$> syn g r
      <|> id  <$> can g r

can :: Scope -> Raw -> Maybe Chk
can g (c :! []) = pure (Can c [])
can g ((c :! []) :$ rs) = Can c <$> traverse (chk g) rs
can _ _ = Nothing


-- Synthesizable terms

data Syn
  = Var Int                   -- de Bruijn variable
  | Syn :/ Chk                -- elim form
  | Rad Chk [(Chk, Chk)] Chk  -- radical
  deriving Show

syn :: Scope -> Raw -> Maybe Syn
syn (is, xs) (x :! []) | Just n <- findIndex (x ==) xs = pure (Var n)
syn g (RadR t ts ty) =
  Rad <$> chk g t <*> traverse chks ts <*> chk g ty
  where
    chks (r0, r1) = (,) <$> chk g r0 <*> chk g r1
syn g (r :$ rs) = foldl (:/) <$> syn g r <*> traverse (chk g) rs
syn _ _ = Nothing


-- Points

poi :: Scope -> Raw -> Maybe Poi
poi g@(is, _) (i :! ts) = foldl scale <$> poix is i <*> pois ts where
  poix _  "0" = Just P0
  poix _  "1" = Just P1
  poix [] _   = Nothing
  poix (i : is) j | i == j = Just (PI P0 P1)  -- top var, branch over endpoints
  poix (i : is) j = psuc <$> poix is j        -- not top var, so weaken
  pois [] = pure []
  pois ((t0, t1) : ts) = (:) <$> ((,) <$> poi g t0 <*> poi g t1) <*> pois ts
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
