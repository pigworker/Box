{-# LANGUAGE TupleSections #-}

module Main where

import Control.Applicative ( liftA2 )
import Control.Monad ( when, forM_ )
import Prelude hiding ( lex )
import System.Directory ( doesFileExist )
import System.Environment ( getArgs )
import System.Exit ( exitFailure )

import Data.Backwards
import Syntax

testCase :: String -> Maybe (String, Chk)
testCase s = do
  let p = eat nom *> eat (tok (TokS ":")) *> raw
  (r, []) <- parse p (lex s)
  (s,) <$> chk (B0, B0) r

process :: FilePath -> IO ()
process fp = do
  test <- doesFileExist fp
  when test $ do
    ls <- lines <$> readFile fp
    maybe exitFailure display $ traverse testCase ls

display :: [(String, Chk)] -> IO ()
display ls = do
  let width = maximum $ map (length . fst) ls
  let padding w str = replicate (w - length str) ' '
  forM_ ls $ \ (l, c) -> do
    putStrLn $ unwords
             [ l
             , padding width l
             , show c
             ]

main :: IO ()
main = do
  files <- getArgs
  mapM_ process files
