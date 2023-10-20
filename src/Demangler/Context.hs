module Demangler.Context
  (
    Context
  , Coord
  , newDemangling
  , contextFindOrAdd
  , contextStr
  )
where

import           Data.Sequence ( (|>) )
import qualified Data.Sequence as Seq
import           Data.Text ( Text )


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

contextStr :: Context -> Coord -> Text
contextStr (Context l) i = l `Seq.index` i
