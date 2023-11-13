{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

-- | This is an internal module that provides the core parsing engine
-- functionality for the Demangler.

module Demangler.Engine
where

import           Control.Applicative
import           Control.Lens ( Lens, Lens', (&), (^.), (.~), _1, _2, _3 )
import           Data.Char
import           Data.List.NonEmpty ( NonEmpty((:|)) )
import           Data.Maybe ( fromMaybe )
import qualified Data.Sequence as Seq
import           Data.Text ( Text )
import qualified Data.Text as T

import           Demangler.Context
import           Demangler.Structure

#ifdef MIN_VERSION_panic
-- The debug flag is enabled in the cabal file
import           Debug.Trace
import           Panic

instance PanicComponent Demangler where
  panicComponentName _ = "Demangler"
  panicComponentIssues = const "https://github.com/galoisinc/demangler/issues"
  panicComponentRevision _ = ("main", "-")

cannot :: PanicComponent a => a -> String -> [String] -> b
cannot = panic
#else
cannot :: a -> String -> [String] -> Maybe b
cannot _ _ _ = Nothing  -- signals a parsing failure, ultimately resulting in Original
#endif

data Demangler = Demangler


type Result = (Demangled, Context)

--------------------
-- Mangled name parsing basis types

-- | Next encodes a parsing step: provided with the current string and the
-- context, it may succeed with the remainder of the string after the portion
-- consumed by this parser and the updated context.

type Next a b = NextArg a -> Maybe (NextArg b)

type NextArg a = (Text, (a, (Context, ( Seq.Seq SubsCandidate
                                      , (Seq.Seq TemplateArg, Bool, Bool)))))

type AnyNext b = forall a . Next a b


nInp :: Lens' (NextArg a) Text
nInp = _1

nVal :: Lens (NextArg a) (NextArg b) a b
nVal = _2 . _1

nContext :: Lens' (NextArg a) Context
nContext = _2 . _2 . _1

nSubs :: Lens' (NextArg a) (Seq.Seq SubsCandidate)
nSubs = _2 . _2 . _2 . _1

nTmplSubs :: Lens' (NextArg a) (Seq.Seq TemplateArg)
nTmplSubs = _2 . _2 . _2 . _2 . _1

nTmplSubsLatch :: Lens' (NextArg a) Bool
nTmplSubsLatch = _2 . _2 . _2 . _2 . _2

nTmplSubsLock :: Lens' (NextArg a) Bool
nTmplSubsLock = _2 . _2 . _2 . _2 . _3

ret :: Applicative f => NextArg a -> b -> f (NextArg b)
ret i v = pure (_2 . _1 .~ v $ i)

ret' :: Applicative f => b -> NextArg a -> f (NextArg b)
ret' a b = ret b a

rmap :: Applicative f => (a -> b) -> NextArg a -> f (NextArg b)
rmap f i = ret i $ f (i ^. nVal)


--------------------
-- Helpers

match :: Text -> Next a a
match n i =
  let (mp, rp) = T.splitAt (T.length n) (i ^. nInp)
  in do require (mp == n)
        pure $ i & nInp .~ rp

single_digit_num :: AnyNext Int
single_digit_num i =
  let txt = i ^. nInp
      d = T.head txt
  in if not (T.null txt) && isDigit d
     then Just $ i & nInp .~ T.drop 1 txt & nVal .~ ord d - ord '0'
     else Nothing

digits_num :: AnyNext Int
digits_num i =
  let (d,r) = T.span isDigit $ i ^. nInp
  in if T.null d
     then Nothing
     else Just $ i & nInp .~ r & nVal .~ read (T.unpack d)

base36_num :: AnyNext Int
base36_num i =
  let isB36char c = or [ isDigit c, isAsciiUpper c ]
      nextB36Digit a x = (a * 36)
                         + (ord x - if isDigit x then ord '0' else ord 'A' - 10)
      (d,r) = T.span isB36char $ i ^. nInp
  in if T.null d
     then Nothing
     else Just $ i & nInp .~ r & nVal .~ T.foldl nextB36Digit 0 d

require :: Bool -> Maybe ()
require t = if t then Just () else Nothing

rdiscard :: NextArg a -> NextArg ()
rdiscard = nVal .~ ()

#if MIN_VERSION_base(4,16,0)
#else
asum :: (Foldable t, Alternative f) => t (f a) -> f a
asum = foldr (<|>) empty
#endif

asum' :: (Foldable t, Functor t, Alternative f) => t (a -> f b) -> a -> f b
asum' opts i = asum $ ($ i) <$> opts

tbd :: String -> Next a b
#ifdef MIN_VERSION_panic
tbd why i = trace ("TBD: " <> why <> " @ " <> (T.unpack $ i ^. nInp)) Nothing
#else
tbd _why = const Nothing
#endif

some' :: AnyNext a -> Next b (NonEmpty a)
some' p i = do e1 <- p i
               go p e1 >>= rmap (e1 ^. nVal :|)
  where go p' i' = case p' i' of
                     Nothing -> ret i' []
                     Just e -> go p' e >>= rmap (e ^. nVal :)

many' :: Next () a -> Next () [a]
many' p i = case p i of
              Nothing -> ret i []
              Just e -> many' p (rdiscard e) >>= rmap (e ^. nVal :)

optional' :: Next a b -> Next a (a, Maybe b)
optional' o i = (o i >>= rmap ((i ^. nVal,) . Just)) <|> rmap (,Nothing) i

(>&=>) :: Next a b -> Next b c -> Next a (b,c)
a >&=> b = \i -> do x <- a i
                    y <- b x
                    rmap ((x ^. nVal,)) y
infixl 2 >&=>

insert :: b -> Next a b
insert v = pure . (nVal .~ v)

noop :: Next a a
noop = Just

end_of_input :: Next a a
end_of_input i = if T.null (i ^. nInp) then Just i else Nothing

#ifdef MIN_VERSION_panic
traceP :: String -> Next a a
traceP at i = trace (at <> " @ " <> (T.unpack $ i ^. nInp) <> " #subs=" <> show (Seq.length (i ^. nSubs)) <> " #tmplSubs=" <> show (Seq.length (i ^. nTmplSubs))) $ Just i
#endif

----------------------------------------------------------------------

-- | Add an additional PrefixR entry to the end of a Prefix.

extendPrefix :: Prefix -> PrefixR -> Prefix
extendPrefix = \case
      PrefixTemplateParam tp PrefixEnd -> PrefixTemplateParam tp
      PrefixDeclType dt PrefixEnd -> PrefixDeclType dt
      Prefix PrefixEnd -> Prefix
      PrefixTemplateParam tp sp -> PrefixTemplateParam tp . extPfx2 sp
      PrefixDeclType dt sp -> PrefixDeclType dt . extPfx2 sp
      Prefix sp -> Prefix . extPfx2 sp
      o -> fromMaybe (const o) $ cannot Demangler "extendPrefix"
           [ "What prefix to extend? " <> show o ]
extPfx2 :: PrefixR -> (PrefixR -> PrefixR)
extPfx2 = \case
      PrefixEnd -> id
      PrefixUQName uqn sp -> PrefixUQName uqn . extPfx2 sp
      PrefixTemplateArgs ta sp -> PrefixTemplateArgs ta . extPfx2 sp

-- | Split a prefix into the last element and the initial portion without that
-- last element (if possible).

prefixInitLast :: Prefix -> Maybe (Prefix, Either UnqualifiedName TemplateArgs)
prefixInitLast = \case
  PrefixTemplateParam tp p2 -> descend (PrefixTemplateParam tp) p2
  PrefixDeclType dt sp -> descend (PrefixDeclType dt) sp
  Prefix p2 -> descend Prefix p2
  o -> cannot Demangler "prefixInitLast"
       [ "Not a valid prefix for this need"
       , show o
       ]
  where
    descend :: (PrefixR -> Prefix) -> PrefixR
            -> Maybe (Prefix, Either UnqualifiedName TemplateArgs)
    descend mkPfx pfxR = let (rf, mb'le) = go (id, Nothing) pfxR
                         in case mb'le of
                              Nothing -> Nothing
                              Just le -> Just (mkPfx $ rf PrefixEnd, le)
    go seen = \case
      PrefixUQName uqn PrefixEnd -> (fst seen, Just $ Left uqn)
      PrefixUQName uqn subpfx ->
        go (fst seen . PrefixUQName uqn, Just $ Left uqn) subpfx
      PrefixTemplateArgs ta PrefixEnd -> (fst seen, Just $ Right ta)
      PrefixTemplateArgs ta subpfx ->
        go (fst seen . PrefixTemplateArgs ta, Just $ Right ta) subpfx
      PrefixEnd -> seen
