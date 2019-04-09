{-# LANGUAGE PatternGuards #-}

module Syntax where

import Prelude hiding (lex)
import Data.Char
import Data.List
import Control.Applicative
import Control.Monad

data Brk = Round | Square | Curly deriving (Show, Eq)

data Tok
  = TokI String
  | TokS String
  | TokO Brk String
  | TokC String Brk
  | TokB Brk String Brk
  deriving (Show, Eq)

solo :: String
solo = ",;?"

isSym :: Char -> Bool
isSym c =
  not (isSpace c) &&
  not (isAlphaNum c) &&
  not (elem c "({[)]}") &&
  not (elem c solo)
  

getOpen :: Char -> Maybe Brk
getOpen '(' = Just Round
getOpen '[' = Just Square
getOpen '{' = Just Curly
getOpen _ = Nothing

getClose :: Char -> Maybe Brk
getClose ')' = Just Round
getClose ']' = Just Square
getClose '}' = Just Curly
getClose _ = Nothing

lex :: String -> [Tok]
lex "" = []
lex cs@(c : s)
  | elem c solo = TokS [c] : lex s
  | isSpace c = lex s
  | isAlphaNum c = case span isAlphaNum s of
    (t, u) -> TokI (c : t) : lex u
  | Just b <- getOpen c = case span isSym s of
    (t, d : u) | Just b' <- getClose d -> TokB b t b' : lex u
    (t, u) -> TokO b t : lex u
  | otherwise = case span isSym cs of
    (t, d : u) | Just b <- getClose d -> TokC t b : lex u
    (t, u) -> TokS t : lex u

newtype Parse x = Parse {parse :: [Tok] -> Maybe (x, [Tok])}
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

tok :: Tok -> Tok -> Maybe ()
tok a b = guard (a == b)

nom :: Tok -> Maybe String
nom (TokI x) = Just x
nom _ = Nothing

sep :: Tok -> Parse a -> Parse [a]
sep s p = (:) <$> p <*> more <|> pure [] where
  more = (:) <$ eat (tok s) <*> p <*> more <|> pure []

data Raw
  = String :! [(Raw,Raw)]
  | Raw :$ [Raw] -- list nonempty
  | String :. Raw
  | String :- Raw
  | RadR Raw [(Raw,Raw)] Raw
  | MetR String [String]
  deriving Show

extn :: Parse [(Raw, Raw)]
extn = id <$ eat (tok (TokO Square "")) <*>
  sep (TokS ",") ((,) <$> raw <* eat (tok (TokS "-")) <*> raw) <*
  eat (tok (TokC "" Square))
  <|> pure []

raw :: Parse Raw
raw = app <$> wee <*> many wee

huge :: Parse Raw
huge = rad <$> raw <*> radex

app :: Raw -> [Raw] -> Raw
app t [] = t
app t ts = t :$ ts

radex :: Parse (Maybe ([(Raw,Raw)], Raw))
radex = Just <$ eat (tok (TokS ":")) <*> ((,) <$> extn <*> raw)
     <|> pure Nothing

rad :: Raw -> Maybe ([(Raw,Raw)], Raw) -> Raw
rad t (Just (ts, ty)) = RadR t ts ty
rad t Nothing = t

wee :: Parse Raw
wee = id <$ eat (tok (TokO Round "")) <*> huge <* eat (tok (TokC "" Round))
  <|> glom <$> eat nom <*> suff
  <|> MetR <$ eat (tok (TokS "?")) <*> eat nom <*>
       many (id <$ eat (tok (TokS "-")) <*> eat nom)
  where
  glom x (Left (True, t)) = x :. t
  glom x (Left (False, t)) = x :- t
  glom x (Right ts) = x :! ts

suff :: Parse (Either (Bool, Raw) [(Raw, Raw)])
suff =  Left <$> ((,) <$>
           (True <$ eat (tok (TokS ".")) <|> False <$ eat (tok (TokS "|")))
            <*> raw)
   <|>  Right <$> extn

data Pat
  = PCan String [Pat]
  | PAbs Pat
  | PHiD Pat
  | Pat0
  | Pat1
  | PMet String (Integer, Integer)
  deriving Show

data Chk
  = Can String [Chk]
  | Abs Chk
  | HiD Chk
  | Syn Syn
  | Poi Poi
  | String :? [Chk]
  deriving Show

data Syn
  = Var Int
  | Syn :/ Chk
  | Rad Chk [(Chk, Chk)] Chk
  deriving Show

data Poi = P0 | P1 | PS Poi | PI Poi Poi deriving (Show, Eq)

type Scope = ([String], [String]) -- yuk

pat :: Scope -> Raw -> Maybe Pat
pat (is, xs) (MetR m us) = pure (PMet m (mkThin is us, mkThin xs us))
pat (is, xs) (x :. r) = PAbs <$> pat (is, x : xs) r
pat (is, xs) (i :- r) = PHiD <$> pat (i : is, xs) r
pat g (c :! []) = pure (PCan c [])
pat g ((c :! []) :$ rs) = PCan c <$> traverse (pat g) rs

mkThin :: [String] -> [String] -> Integer
mkThin [] _ = 0
mkThin (x : xs) ys | elem x ys = 2 * mkThin xs ys
                   | otherwise = 2 * mkThin xs ys + 1

psuc :: Poi -> Poi
psuc P0 = P0
psuc P1 = P1
psuc p = PS p

pif0 :: Poi -> Poi -> Poi
pif0 p0 p1 | p0 == p1  = psuc p0
           | otherwise = PI p0 p1

scale :: Poi -> (Poi, Poi) -> Poi
scale P0 (p0, p1) = p0
scale P1 (p0, p1) = p1
scale _ (p0, p1) | p0 == p1 = p0
scale (PS p) (PS p0, PS p1) = psuc (scale p (p0, p1))
scale p (p0, p1) = pif0 (scale (pr0 p) (pr0 p0, pr0 p1))
                        (scale (pr1 p) (pr1 p0, pr1 p1))
  where
  pr0 (PS p) = p
  pr0 (PI p _) = p
  pr0 p = p
  pr1 (PS p) = p
  pr1 (PI _ p) = p
  pr1 p = p

poi :: Scope -> Raw -> Maybe Poi
poi g@(is, _) (i :! ts) = foldl scale <$> poix is i <*> pois ts where
  poix [] "0" = Just P0
  poix [] "1" = Just P1
  poix [] _   = Nothing
  poix (i : is) j | i == j = Just (PI P0 P1)
  poix (i : is) j = psuc <$> poix is j
  pois [] = pure []
  pois ((t0, t1) : ts) = (:) <$> ((,) <$> poi g t0 <*> poi g t1) <*> pois ts
poi _ _ = Nothing

chk :: Scope -> Raw -> Maybe Chk
chk (is, xs) (x :. r) = Abs <$> chk (is, x : xs) r
chk (is, xs) (i :- r) = HiD <$> chk (i : is, xs) r
chk g (MetR x _) = pure (x :? [])
chk g (MetR x _ :$ rs) = (x :?) <$> traverse (chk g) rs
chk g r = Poi <$> poi g r
      <|> Syn <$> syn g r
      <|> id <$> can g r

can :: Scope -> Raw -> Maybe Chk
can g (c :! []) = pure (Can c [])
can g ((c :! []) :$ rs) = Can c <$> traverse (chk g) rs
can _ _ = Nothing

syn :: Scope -> Raw -> Maybe Syn
syn (is, xs) (x :! []) | Just n <- findIndex (x ==) xs = pure (Var n)
syn g (RadR t ts ty) =
  Rad <$> chk g t <*> traverse chks ts <*> chk g ty
  where
    chks (r0, r1) = (,) <$> chk g r0 <*> chk g r1
syn g (r :$ rs) = foldl (:/) <$> syn g r <*> traverse (chk g) rs
syn _ _ = Nothing

chkMe :: Scope -> String -> Maybe Chk
chkMe g s = do
  (r, []) <- parse raw (lex s)
  chk g r

patMe :: Scope -> String -> Maybe Pat
patMe g s = do
  (r, []) <- parse raw (lex s)
  pat g r
