{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Demangler.Substitution
  (
    -- * Parse a substitution reference
    substitution
    -- * Substitute the found substitution into the result
  , substituteUnqualifiedName
  , substitutePrefix
  , substitutePrefixR
  , substituteTemplateParam
  , substituteTemplatePrefix
  , substituteType
  , stdSubstToType
  , substituteUnresolvedType
  -- * When a subtitution candidate has been parsed, it is recorded here
  , canSubstUnscopedTemplateName
  , canSubstPrefix
  , canSubstTemplateArg
  , canSubstTemplateParam
  , canSubstTemplatePrefix
  , canSubstType
  , canSubstTypes
  , canSubstUnresolvedType
  , dropLastSubst
  )
where

import           Control.Applicative
import           Control.Lens ( (&), (^.), (%~) )
import           Control.Monad
import           Data.List.NonEmpty ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty as NEL
import           Data.Maybe
import           Data.Sequence ( (|>), ViewR((:>)) )
import qualified Data.Sequence as Seq

import           Demangler.Engine
import           Demangler.Structure
import           Demangler.PPrint ()

#ifdef MIN_VERSION_panic
-- The debug flag is enabled in the cabal file
import           Demangler.Context
import           Text.Sayable
import           Debug.Trace
#endif

import           Prelude hiding ( last )


--------------------
-- * Handling Substitutions
--
-- Substition could be handled at parsing time or at pretty-printing time.  This
-- implementation handles substitution at parsing time for the following reasons:
--
--  1. Parser "type" information to confirm that the substitution value is
--     appropriate to be substituted in the current parsing element.
--
--  2. The resulting Demangled structure is fully expressed and does not need to
--     hold additional "sequencing" information that would allow Substitution
--     target identification.  Also simplifies use of the Demangled structure.
--
--  3. The sequencing information can also be more difficult to re-determine at
--     pretty-printing time (viz. the efforts in the itanium-abi package which
--     performs substitution at pretty-printing time).
--
-- Substitution is very tricky: the BNF (at the URL in the Dismantle module, and
-- which isn't fully correct) specifies that wherever "<substitution>" appears, a
-- substitution may be made OR a substitution capture can occur.  It also states
-- that substitutions are not duplicated.  It implies (but is not clear) that
-- there are actually two substitution namespaces: regular substitutions and
-- template subsitutions, where the former are accessed as "S[n]_" and the latter
-- are accessed as "T[m]_", where the n and m ordering are within the associated
-- namespace.  Here are the additional rules and exceptions not discussed:
--
--   * Constructor/Destructor names are not captured or substituted (but operator
--     names are)
--
--   * Known substitutions ("St" for "std::", "Sa" for "std::allocator", etc.)
--     are *not* added as a possible substitution if they appear alone, but if
--     they are part of a prefix (i.e. they are followed by other information)
--     then they are added as part of that longer sequence (e.g. "foo::list<i>"
--     will add "foo", "foo::list", and "foo::list<i>" for a total of 3 possible
--     substitution candidates whereas "std::list<i>" will add "std::list" and
--     "std::list<i>" for only 2 possible substitution candidates.
--
--   * Template argument substutions are in a different namespace and recursive
--     template arguments are not substitition candidates (e.g. foo<bar<int>>)
--     results in only one template substitution candidate (bar<int>).


-- | Parse a substitution specification and get the raw Substitution' result;
-- these should always be translated and never actually returned in the Demangled
-- result.

substitution :: AnyNext Substitution'
substitution =
  asum' [ match "S" >=> base36_num >=> rmap (Subs . toEnum) >=> match "_"
        , match "S_" >=> rmap (const SubsFirst)
        , match "St" >=> rmap (const $ SubsConst SubStd)
        , match "Sa" >=> rmap (const $ SubsConst SubAlloc)
        , match "Sb" >=> rmap (const $ SubsConst SubBasicString)
        , match "Ss" >=> rmap (const $ SubsConst $ SubStdType BasicStringChar)
        , match "Si" >=> rmap (const $ SubsConst $ SubStdType BasicIStream)
        , match "So" >=> rmap (const $ SubsConst $ SubStdType BasicOStream)
        , match "Sd" >=> rmap (const $ SubsConst $ SubStdType BasicIOStream)
        ]

-- Internal to lookup a parsed Substitution'
getSubst :: NextArg Substitution' -> Either Substitution (Maybe SubsCandidate)
getSubst i =
  case i ^. nVal of
    SubsFirst -> Right $ Seq.lookup 0 $ i ^. nSubs
    Subs n -> Right $ Seq.lookup (fromEnum n + 1) $ i ^. nSubs
    SubsConst s -> Left s


#ifdef MIN_VERSION_panic
dumpSubs :: (Monad f, Applicative f)
         => NextArg a -> String -> f (NextArg a)
dumpSubs spec what = do
    mapM_ (traceM . show) $ Seq.zip
             (Seq.fromList [0.. Seq.length (spec ^. nSubs)])
             ((\ue -> (ue, sez @"debug" (addContext ue (spec ^. nContext))))
              <$> spec ^. nSubs)
    mapM_ (traceM . show) $ Seq.zip
             (Seq.fromList [0.. Seq.length (spec ^. nTmplSubs)])
             ((\ue -> ('T', ue, sez @"debug" (addContext ue (spec ^. nContext))))
              <$> spec ^. nTmplSubs)
    traceM $ "Subs Total: " <> show ((Seq.length $ spec ^. nSubs) + (Seq.length $ spec ^. nTmplSubs)) <> " "
        <> show ((Seq.length $ spec ^. nSubs), (Seq.length $ spec ^. nTmplSubs))
        <> " --> " <> sez @"debug" what
    pure spec
#endif

invalidSubst :: Show a => String -> NextArg a -> Maybe SubsCandidate -> Maybe b
invalidSubst for spec = \case
  Just s -> do
#ifdef MIN_VERSION_panic
    -- Debug details
    _ <- dumpSubs spec "Just"
#endif
    cannot Demangler for
         [ "Invalid " <> for <> " substitution (" <> show (spec ^. nVal) <> "):"
         , show s
         ]
  Nothing -> do
#ifdef MIN_VERSION_panic
    -- Debug details
    _ <- dumpSubs spec "Nothing"
#endif
    cannot Demangler for
         [ "Invalid " <> for <> " substitution reference:"
         , show (spec ^. nVal)
         ]

substituteUnqualifiedName :: Next Substitution UnqualifiedName
                          -> Next Substitution' UnqualifiedName
substituteUnqualifiedName direct i =
  case getSubst i of
    Right (Just (SC_UQName _ n)) -> ret i n
    Right _ -> Nothing
    Left s -> direct =<< ret i s

substituteType :: (Next Substitution Type_) -> Next Substitution' Type_
substituteType embed i =
  case getSubst i of
    Right (Just (SC_Type t)) -> ret i t
    Right (Just (SC_Prefix p)) -> ret i =<< prefixToType p
    Right (Just (SC_UQName isStd uqn)) ->
      ret i $ ClassUnionStructEnum $ UnscopedName isStd uqn
    Right o -> invalidSubst "Type" i o
    Left s -> embed =<< ret i s


prefixToType :: Prefix -> Maybe Type_
prefixToType pfx =
  ClassUnionStructEnum
  <$> case prefixInitLast pfx of
      Nothing -> cannot Demangler "prefixToType"
                 [ "Cannot convert prefix to type: " <> show pfx ]
      Just (iniPfx, Left uqn) ->
        Just $ NameNested $ NestedName iniPfx uqn [] Nothing
      Just (iniPfx, Right ta) ->
        let tmpltpfx =
              case prefixInitLast iniPfx of
                Just (EmptyPrefix, Left luqn) ->
                  Just $ GlobalTemplate (luqn :| [])
                Just (p, Left luqn) ->
                  Just $ NestedTemplate p (luqn :| [])
                _ -> cannot Demangler "prefixToType"
                     [ "Cannot convert ta prefix to type: " <> show pfx ]
            mkntn tpfx = NestedTemplateName tpfx ta [] Nothing
        in NameNested . mkntn <$> tmpltpfx

substituteUnresolvedType :: Next Substitution UnresolvedType
                         -> Next Substitution' UnresolvedType
substituteUnresolvedType direct i =
  case getSubst i of
    Right (Just (SC_Prefix p)) -> ret i $ URTSubstPrefix p
    Right (Just (SC_UnresolvedType urt)) -> ret i urt
    Right x -> cannot Demangler "substituteUnresolvedType"
               [ "Cannot convert to an unresolved type: " <> show x ]
    Left s -> direct =<< ret i s

substitutePrefix :: Next Substitution Prefix -> Next Substitution' Prefix
substitutePrefix direct i =
  case getSubst i of
    Right (Just (SC_Prefix p)) -> ret i p
    Right o -> invalidSubst "Prefix" i o
    Left s -> direct =<< ret i s

substitutePrefixR :: Next Substitution PrefixR -> Next Substitution' PrefixR
substitutePrefixR direct i =
  case getSubst i of
    Right o@(Just (SC_Type (ClassUnionStructEnum nm))) ->
      case name2prefix nm of
        Just pfx -> ret i pfx
        Nothing -> invalidSubst "PrefixR.SC_Type.ClassUnionStructEnum" i o
    Right (Just (SC_Prefix (Prefix sp))) -> ret i sp
    Right o -> invalidSubst "PrefixR" i o
    Left s -> ret i s >>= direct
  where
    name2prefix = \case
      NameNested nn -> nn2prefix nn
      UnscopedName True uqn -> Nothing
        -- Just $ PrefixUQName (SourceName (!!! "std") mempty) $ PrefixUQName uqn PrefixEnd
      UnscopedName False uqn -> Just $ PrefixUQName uqn PrefixEnd
      UnscopedTemplateName nm _tmplArgs -> name2prefix nm
      LocalName _enc nm _disc -> name2prefix nm -- discriminators are invisible
      StringLitName _ _ -> Nothing
    nn2prefix = \case
      NestedName pf@(Prefix _) uqn _cvq _mbref ->
        case extendPrefix pf $ PrefixUQName uqn PrefixEnd of
          Prefix pfr -> Just pfr
          _ -> Nothing
      o -> Nothing


substituteTemplatePrefix :: (Next Substitution TemplatePrefix)
                         -> Next Substitution' TemplatePrefix
substituteTemplatePrefix direct i =
  case getSubst i of
    Right o@(Just (SC_Prefix (Prefix p2))) ->
      let go = \case
            PrefixEnd -> Nothing
            PrefixUQName uqn sp ->
              case go sp of
                Nothing -> Just $ GlobalTemplate $ uqn :| []
                Just (GlobalTemplate uqns) ->
                  Just $ GlobalTemplate $ NEL.cons uqn uqns
                Just (NestedTemplate (Prefix p) uqns) ->
                  Just $ NestedTemplate (Prefix $ PrefixUQName uqn p) uqns
                _ -> Nothing -- ??
            PrefixTemplateArgs ta sp ->
              case go sp of
                Nothing -> Nothing
                Just (GlobalTemplate uqns) ->
                  Just $ NestedTemplate (Prefix $ PrefixTemplateArgs ta PrefixEnd) uqns
                Just (NestedTemplate (Prefix p) uqns) ->
                  Just $ NestedTemplate (Prefix $ PrefixTemplateArgs ta p) uqns
                _ -> Nothing -- ??
      in case go p2 of
           Nothing -> invalidSubst "Template Prefix (2)" i o
           Just o' -> ret i o'
    Right (Just (SC_Prefix (PrefixTemplateParam p PrefixEnd))) ->
      ret i $ TemplateTemplateParam p
    Right o -> invalidSubst "Template Prefix" i o
    Left s -> ret i s >>= direct


-- | Calls to replace a template substitution ("T[n]_") with the replacement
-- value from the original template argument specification.  Note that these
-- substitutions are independent of the normal substitutions (i.e. "S[n]_").

substituteTemplateParam :: Next (Maybe Int) TemplateParam
substituteTemplateParam i =
  let idx = maybe 0 (+1) $ i ^. nVal
  in case Seq.lookup idx (i ^. nTmplSubs) of
       Just a -> ret i a
       _ ->
#ifdef MIN_VERSION_panic
            -- Debug details
            dumpSubs i "Nothing Template Param" >>
#endif
            cannot Demangler "substituteTemplateParam"
              [ "Invalid Template Param substitution reference: "
              , show (i ^. nVal)
              ]


-- | Called during parsing to add a SubsCandidate for future Substitution lookup.

canSubst :: SubsCandidate -> Next a a
canSubst what i = pure $ i & nSubs %~ (|> what)

dropLastSubst :: Next a a
dropLastSubst i = pure $ i & nSubs %~ dropLast
  where dropLast s = case Seq.viewr s of
                       Seq.EmptyR -> s
                       s' :> _ -> s'

-- | Called during parsing to add an unscoped template name for future
-- Substitution lookup.
canSubstUnscopedTemplateName :: Next Name Name
canSubstUnscopedTemplateName i =
  case i ^. nVal of
    UnscopedName isStd uqn -> canSubst (SC_UQName isStd uqn) i
    _ -> pure i


-- | Called during parsing to add a NamePrefix SubsCandidate for future
-- Substitution lookup.  This one is a bit different because the Prefix may
-- contain a NonEmpty list of Unqualified names: each init of that list is a
-- substitutable.
canSubstPrefix :: Next Prefix Prefix
canSubstPrefix i = canSubst (SC_Prefix $ i ^. nVal) i

-- | Called during parsing to add an Type_ SubsCandidate for future Substitution
-- lookup.

canSubstType :: Next Type_ Type_
canSubstType i = canSubst (SC_Type $ i ^. nVal) i

canSubstTypes :: Next (NEL.NonEmpty Type_) (NEL.NonEmpty Type_)
canSubstTypes i =
  let subT i' ty = canSubst (SC_Type $ ty) i'
  in foldM subT i (i ^. nVal)

canSubstUnresolvedType :: Next UnresolvedType UnresolvedType
canSubstUnresolvedType i = canSubst (SC_UnresolvedType $ i ^. nVal) i

canSubstTemplatePrefix :: Next TemplatePrefix TemplatePrefix
canSubstTemplatePrefix i = canSubst (SC_TemplatePrefix $ i ^. nVal) i

canSubstTemplateParam :: Next TemplateParam TemplateParam
canSubstTemplateParam = canSubstTemplateArg

canSubstTemplateArg :: Next TemplateArg TemplateArg
canSubstTemplateArg i =
  if i ^. nTmplSubsLock
  then pure i
  else pure $ i & nTmplSubs %~ (|> (i ^. nVal))

----------------------------------------------------------------------

stdSubstToType :: Next Substitution Type_
stdSubstToType i =
  case (i ^. nVal) of
    SubStdType stdTy -> ret i $ StdType stdTy
    s -> cannot Demangler "stdSubstToType"
         [ "Substitution " <> show s <> " is not a type" ]
