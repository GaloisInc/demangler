{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK prune #-}

module Demangler.Context
  (
    Context
  , Coord
  , newDemangling
  , contextFindOrAdd
  , contextStr
  , WithContext
  , addContext
  , withContext
  , contextData
  , withContextForTemplateArg
  , isTemplateArgContext
  , sayableConstraints
  )
where

import           Data.Sequence ( (|>) )
import qualified Data.Sequence as Seq
import           Data.Text ( Text )
import qualified Language.Haskell.TH as TH

import Text.Sayable


-- | The Context provides a persistent information and collection over a set of
-- demangling calls.  This allows for additional efficiency in memory storage.

-- Note that it can be observed that the stored data here is identifiers, and
-- therefore there are 64 initial characters ('A-Za-z0-9_' + 1 bucket for all
-- others).  This might lead to the use of an Array of Seq or an IntMap of Seq.
-- Both of these were tested in both single and batched mode against
-- approximately 13,000 demanglings: there was no significant different between
-- those more complicated forms and this simple Seq in either time, memory
-- consumption, or garbage collection, so this simplest form is sufficient.

data Context = Context (Seq.Seq Text)

-- | Return an initial Context useable for calls to 'demangle'.

newDemangling :: Context
newDemangling = Context mempty

type Coord = Int


contextFindOrAdd :: Text -> Context -> (Coord, Context)
contextFindOrAdd s c@(Context l) =
  case Seq.elemIndexL s l of
    Just n -> (n, c)
    Nothing -> (Seq.length l, Context $ l |> s)

contextStr :: WithContext a -> Coord -> Text
contextStr (WC _ _ (Context l)) i = l `Seq.index` i

data SayingElement = DefaultSay | SayingTemplateArg

data WithContext a = WC  SayingElement a Context

addContext :: a -> Context -> WithContext a
addContext = WC DefaultSay

withContext :: WithContext a -> b -> WithContext b
withContext (WC s _ c) d = WC s d c

withContextForTemplateArg :: WithContext a -> b -> WithContext b
withContextForTemplateArg (WC _ _ c) d = WC SayingTemplateArg d c

isTemplateArgContext :: WithContext a -> Bool
isTemplateArgContext (WC SayingTemplateArg _ _) = True
isTemplateArgContext _ = False

contextData :: WithContext a -> a
contextData (WC _ d _) = d

sayableConstraints :: TH.Name -> TH.PredQ
sayableConstraints forTy = do
  let rTy = TH.ConT forTy
  wctxt <- [t|WithContext|]
  sayableSubConstraints $ do ofType forTy
                             paramTH rTy
                             subElemFilter (not
                                            . (`elem` [ "Context"
                                                      , "Bool"
                                                      , "Natural"
                                                      , "Float"
                                                      ])
                                             . TH.nameBase)
                             subWrapper wctxt
                             tagVar "saytag"
