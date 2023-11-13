{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Demangler.Accessors
  (
    functionName
  )
where

import           Data.List.NonEmpty ( NonEmpty( (:|) ) )
import qualified Data.List.NonEmpty as NEL
import           Data.Text ( Text )
import qualified Data.Text as T

import           Demangler.Context
import           Demangler.Engine
import           Demangler.Structure


-- | Returns the base function name.  This is the core text name for the function
-- (C-style) followed by the parent class/namespace (innermost-to-outermost) but
-- without any argument and template information and therefore it is not
-- necessarily unique.  The parent names have any template information removed as
-- well. For example:
--
-- @std::map<int, char>::insert(...)@ returns @"insert" :| [ "map", "std" ]@
--
-- The reason for the reversed form is that the base name is usually the most
-- relevant, and the parent information can be optionally consumed (and lazily
-- generated) as needed.
--
-- If the name could not be demangled, the non-demangled form is returned
-- (perhaps it is a plain function name already?).
--
-- If the demangled name is not a function (e.g. a data or special name) then
-- Nothing is returned.

functionName :: Result -> Maybe (NEL.NonEmpty Text)
functionName (d,c) =
  case d of
    Original i -> Just $ contextStr c i :| []
    Encoded e -> resolveCtorDtor <$> (getEnc $ traceShowId e)
    VendorExtended e _ -> getEnc e
  where
    resolveCtorDtor = \case
      ("{{CTOR}" :| r@(nm : _)) -> nm :| r
      ("{{DTOR}" :| r@(nm : _)) -> "~" <> nm :| r
      o -> o
    getEnc = \case
      EncFunc (FunctionName fn) _rty _argtys -> getName fn
      EncStaticFunc (FunctionName fn) _rty _argtys -> getName fn
      _ -> Nothing
    getName = \case
      UnscopedName False uqn -> Just $ NEL.fromList $ getUQN uqn
      UnscopedName True uqn -> Just $ NEL.fromList $ getUQN uqn <> ["std"]
      UnscopedTemplateName nm _tmplArgs -> getName nm
      NameNested nnm -> getNestedNm nnm
      nm -> Just $ T.pack ( show nm ) :| []
    getUQN = \case
      SourceName (SrcName i) _ -> [contextStr c i]
      OperatorName op _ ->
        [maybe (T.pack $ show op) (("operator" <>) . snd . snd)
         $ lookup op opTable]
      CtorDtorName ctd -> case ctd of
                            CompleteCtor -> ["{{CTOR}"]
                            BaseCtor -> ["{{CTOR}"]
                            CompleteAllocatingCtor -> ["{{CTOR}"]
                            CompleteInheritingCtor _ -> ["{{CTOR}"]
                            BaseInheritingCtor _ -> ["{{CTOR}"]
                            DeletingDtor -> ["{{DTOR}"]
                            CompleteDtor -> ["{{DTOR}"]
                            BaseDtor -> ["{{DTOR}"]
      StdSubst sbst -> case sbst of
                         SubStd -> ["std"]
                         SubAlloc -> [ "allocator", "std" ]
                         SubBasicString -> [ "basic_string", "std" ]
                         SubStdType BasicStringChar -> [ "string", "std" ]
                         SubStdType BasicIStream -> [ "istream", "std" ]
                         SubStdType BasicOStream -> [ "ostream", "std" ]
                         SubStdType BasicIOStream -> [ "iostream", "std" ]
      ModuleNamed _ uqn -> getUQN uqn
    getNestedNm = \case
      NestedName pfx uqn _ _ -> NEL.nonEmpty $ getUQN uqn <> getPfx pfx
      NestedTemplateName tmplpfx _tmplArgs _ _ -> NEL.nonEmpty $ getTmplPfx tmplpfx
    getPfx = \case
      PrefixTemplateParam _tmplParam r -> getPfxR r
      PrefixDeclType _dclTy r -> getPfxR r
      PrefixClosure _ -> []
      Prefix r -> getPfxR r
    getPfxR = \case
      PrefixUQName uqn r -> getPfxR r <> getUQN uqn
      PrefixTemplateArgs _ r -> getPfxR r
      PrefixEnd -> []
    getTmplPfx = \case
      GlobalTemplate uqns -> foldr ((<>) . getUQN) [] uqns
      NestedTemplate pfx uqns -> foldr ((<>) . getUQN) (getPfx pfx) uqns
      TemplateTemplateParam _ -> []
