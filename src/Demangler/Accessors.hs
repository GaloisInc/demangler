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
-- > std::map<int, char>::insert(...)
--
-- returns:
--
-- > "insert" :| [ "map", "std" ]
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
    Original i -> Just $ contextStr (addContext () c) i :| []
    Encoded e -> resolveCtorDtor <$> getEnc e
    VendorExtended e _ -> getEnc e
  where
    resolveCtorDtor = \case
      ("{{CTOR}" :| r@(nm : nm2 : _)) | "unnamed_type_num" `T.isPrefixOf` nm -> nm2 :| r
      ("{{DTOR}" :| r@(nm : nm2 : _)) | "unnamed_type_num" `T.isPrefixOf` nm -> "~" <> nm2 :| r
      ("{{CTOR}" :| r@(nm : _)) -> nm :| r
      ("{{DTOR}" :| r@(nm : _)) -> "~" <> nm :| r
      o -> o
    getEnc = \case
      EncFunc (FunctionName fn) _rty _argtys -> getName fn
      EncStaticFunc (FunctionName fn) _rty _argtys -> getName fn
      EncData (LocalName enc _ _) -> getEnc enc
      _ -> Nothing
    getName = \case
      UnscopedName usn -> getUSN usn
      UnscopedTemplateName nm _tmplArgs -> getName nm
      NameNested nnm -> getNestedNm nnm
      nm -> Just $ T.pack ( show nm ) :| []
    getUSN = \case
      UnScName False uqn -> Just $ NEL.fromList $ getUQN uqn
      UnScName True uqn -> Just $ NEL.fromList $ getUQN uqn <> ["std"]
      UnScSubst subs -> Just $ NEL.fromList $ getStdSubst subs
    getUQN = \case
      SourceName (SrcName i) _ -> [contextStr (addContext () c) i]
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
      StdSubst sbst -> getStdSubst sbst
      ModuleNamed _ uqn -> getUQN uqn
      UnnamedTypeName mbnum ->
        -- Highly unusual, and probably not ultimately useful.  This happens when
        -- an unnamed structure/union/class has a function.  For example,
        -- "_ZN3FooUt3_C2Ev" translates to "Foo::{unnamed type#5}::Foo()".
        let n = maybe 1 (+2) mbnum in [ T.pack $ "unnamed_type_num" <> show n ]
    getStdSubst = \case
      SubStd -> ["std"]
      SubAlloc -> [ "allocator", "std" ]
      SubBasicString -> [ "basic_string", "std" ]
      SubStdType BasicStringChar -> [ "string", "std" ]
      SubStdType BasicIStream -> [ "istream", "std" ]
      SubStdType BasicOStream -> [ "ostream", "std" ]
      SubStdType BasicIOStream -> [ "iostream", "std" ]
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
