{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Control.Monad.Trans.State
import qualified Data.Text as T
import           System.Environment
import           System.Exit
import           Text.Sayable

import           Demangler ( demangle, demangle1, newDemangling )


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> mapM_ (const
                 (putStrLn . sez_ @"diagnostic" . demangle1 . T.pack =<< getLine)
                ) [0 :: Integer ..]
    ("--help":[]) ->
      do putStrLn "Translates C++ mangled names"
         me <- getProgName
         putStrLn $ "Usage: " <> me <> " [mangled-name ...]"
         putStrLn "If no names are provided on the command line, stdin is read"
         putStrLn "Names which fail translation are echoed with a {orig} final word."
         exitSuccess
    o -> let r = runState (sequence (state . demangle . T.pack <$> o)) newDemangling
         in mapM_ (putStrLn . sez_ @"diagnostic" . (,snd r)) $ fst r
  putStrLn "{done}"
