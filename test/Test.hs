{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import           Control.Monad.Trans.State
import           Data.Text ( Text )
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PRT
import           System.Process
import           Test.Hspec
import           Test.Tasty
import           Test.Tasty.Hspec
import           Text.Sayable

import           Demangler ( demangle, demangle1, newDemangling )

-- n.b. Original conception was to use a Sandwich Context to retrieve the
-- contents of the input data files, but a Context can only be retrieved (via
-- getContext) inside an ExampleT, which is the body of an `it "something" body`
-- statement.  Thus, there's no way to iterate over the individual lines of the
-- input file and create an ExampleT test for each one.

main :: IO ()
main = do inps <- mapM getInputData  [ "test/initial-test-cases.txt"
                                     , "test/full-test-cases.txt"
                                     ]
          defaultMain =<< (testSpec "Demangle" $ demangleTests inps)


getInputData :: String -> IO (String, [(Text, Text)])
getInputData fname = do
  inputs <- TIO.readFile fname
  expects <- T.pack <$> readProcess "c++filt" [] (T.unpack inputs)
  let pairs = zip (T.lines inputs) (T.lines expects)
  return (fname, pairs)


demangleTests :: [(String, [(Text, Text)])] -> Spec
demangleTests testInputs = describe "Demangle tests" $
                           mapM_ demangleTestSet testInputs

demangleTestSet :: (String, [(Text, Text)]) -> Spec
demangleTestSet (inpFile, inpData) =
  describe inpFile $
  do describe "Individually" $ sequence_ (mkTest <$> inpData)
     describe "Batched" $ batchTest inpData


mkTest :: (Text, Text) -> Spec
mkTest (sym, expected) = it ("demangles " <> T.unpack sym) $
  (toText $ demangle1 sym) `shouldBe` expected

batchTest :: [(Text, Text)] -> Spec
batchTest symbols =
  let r = runState (sequence (state . demangle . fst <$> symbols)) newDemangling
      mkRes (dm, (inp, ex)) prs = (inp, toText (dm, snd r), ex) : prs
      results = foldr mkRes [] $ zip (fst r) symbols
      validate (i,rslt,e) = it ("demangles " <> T.unpack i) $ rslt `shouldBe` e
  in sequence_ (validate <$> results)

toText :: Sayable "normal" a => a -> Text
toText = PRT.renderStrict
         . PP.layoutPretty (PP.LayoutOptions PP.Unbounded)
         . saying . sayable @"normal"
