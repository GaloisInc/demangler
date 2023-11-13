{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import           Control.Monad ( unless )
import           Control.Monad.Trans.State
import qualified Data.List.NonEmpty as NEL
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

import           Demangler ( demangle, demangle1, newDemangling, functionName )

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


getInputData :: String -> IO (String, [(Text, Text, [Text])])
getInputData fname = do
  inputs <- TIO.readFile fname
  expects <- T.pack <$> readProcess "c++filt" [] (T.unpack inputs)
  funcNames <- fmap (T.splitOn (T.pack "`"))
               . T.lines
               <$> TIO.readFile (fname <> "-funcnames")
  let matches = zip3 (T.lines inputs) (T.lines expects) (funcNames <> repeat [])
  return (fname, matches)


demangleTests :: [(String, [(Text, Text, [Text])])] -> Spec
demangleTests testInputs = describe "Demangle tests" $
                           mapM_ demangleTestSet testInputs

demangleTestSet :: (String, [(Text, Text, [Text])]) -> Spec
demangleTestSet (inpFile, inpData) =
  describe inpFile $
  do describe "Solo" $ sequence_ (mkTest <$> inpData)
     describe "Batched" $ batchTest inpData


mkTest :: (Text, Text, [Text]) -> Spec
mkTest (sym, expected, funcNames) = describe (T.unpack sym) $ do
  let dm = demangle1 sym
  it "demangles" $ (toText $ dm) `shouldBe` expected
  unless (null funcNames || funcNames == [T.pack ""]) $
    it "gets functionName" $
    (NEL.toList <$> functionName dm) `shouldBe` Just funcNames

batchTest :: [(Text, Text, [Text])] -> Spec
batchTest symbols =
  let r = runState (sequence (state . demangle <$> syms)) newDemangling
      syms = (\(a,_,_) -> a) <$> symbols
      results = foldr mkRes [] $ zip (fst r) symbols
      mkRes (dm, (inp, ex, fne)) prs =
        (inp, toText (dm, snd r), ex, functionName (dm, snd r), fne) : prs
      validate (i,rslt,e,fn,fne) = do
        it ("demangles " <> T.unpack i) $ rslt `shouldBe` e
        unless (null fne || fne == [T.pack ""]) $
          it ("functionName " <> T.unpack i) $ (NEL.toList <$> fn) `shouldBe` Just fne
  in sequence_ (validate <$> results)

toText :: Sayable "normal" a => a -> Text
toText = PRT.renderStrict
         . PP.layoutPretty (PP.LayoutOptions PP.Unbounded)
         . saying . sayable @"normal"
