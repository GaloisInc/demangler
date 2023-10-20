{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Demangler.PPrint () where

import           Data.Char
import           Data.List.NonEmpty ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty as NEL
import           Data.Text ( Text )
import qualified Data.Text as T
import           Text.Sayable

import           Demangler.Context
import           Demangler.Engine
import           Demangler.Structure


#ifdef MIN_VERSION_panic
import Panic

-- Debug function to cause a Panic with -fdebug builds, or return a placeholder
-- in non-debug mode.  This is usually used for unfinished portions of the
-- output, to provide a useful panic when in development mode but to avoid
-- crashing in normal mode.  Note that the demangling process uses a similar
-- function to fail the parse; here, the parse has completed and we are simply
-- generating output, so we don't have the option to "revert" to the original.
-- Instead, emitting invalid output (without failing) is the most useful
-- operation, since the valid form of that output is not currently
-- known/implemented.
cannotSay :: PanicComponent a => a -> String -> [String] -> b
cannotSay = panic
#else
cannotSay :: a -> String -> [String] -> Saying saytag
cannotSay _ _ rsn = t'"OUTFMT?:{ " &* rsn &- '}'
#endif


----------------------------------------------------------------------
-- Sayable instances for printing demangled results

instance {-# OVERLAPPING #-}
  ( Sayable "diagnostic" (Encoding, Context)
  ) => Sayable "diagnostic" Result where
  sayable = \case
    (Original i, c) -> contextStr c i &- t'"{orig}"
    (Encoded e, c) -> sayable @"diagnostic" (e,c)
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr c i
      in (d,c) &- t'"[clone" &- s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Encoding, Context)
  ) => Sayable saytag Result where
  sayable = \case
    (Original i, c) -> sayable @saytag $ contextStr c i
    (Encoded e, c) -> sayable @saytag (e,c)
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr c i
      in (d,c) &- t'"[clone" &- '.' &+ s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Name, Context)
  , Sayable saytag (Type_, Context)
  , Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (SpecialName, Context)
  , Sayable saytag (CVQualifier, Context)
  ) => Sayable saytag (Encoding, Context) where
  sayable (n,c) =
    case n of
      -- Note: if the function has only a single void argument, print "()"
      -- instead of "(void)"; these are semantically the same, but demangling
      -- emits the former.
      --
      -- Another tricky part is that the FunctionName may contain qualifiers
      -- (esp. "const") but for a function these must be placed at the end,
      -- following the arguments.
      EncFunc f rty (BaseType Void :| []) -> sayFunction c f rty []
      EncFunc f rty t -> sayFunction c f rty $ NEL.toList t
      -- n.b. static functions don't have any visible difference in demangled
      -- form.
      EncStaticFunc f rty (BaseType Void :| []) -> sayFunction c f rty []
      EncStaticFunc f rty t -> sayFunction c f rty $ NEL.toList t
      EncConstStructData nm -> sayable @saytag (nm,c)
      EncData nm -> sayable @saytag (nm,c)
      EncSpecial sn -> sayable @saytag (sn,c)

sayFunction :: Context -> FunctionName -> Maybe Type_ -> [Type_] -> Saying saytag
sayFunction c fn mbRet args =
  let (nm,q) = cleanFunctionName fn
      part1 = case mbRet of
                Nothing -> (nm,c) &+ t'""
                Just rty -> (rty, c) &- (nm,c)
      part2 = part1 &+ '(' &+* zip args (repeat c) &+ ')'
  in if null q then part2 else part2 &- ctxLst' q c " "

ctxLst :: forall saytag t a .
          Sayable saytag (a, Context)
       => Functor t
       => Foldable t
       => t a -> Context -> Saying saytag
ctxLst l c = t'"" &+* ((,c) <$> l)

ctxLst' :: Sayable saytag (a, Context)
        => Functor t
        => Foldable t
        => t a -> Context -> Text -> Saying saytag
ctxLst' l c sep = sep &:* ((,c) <$> l)

cleanFunctionName :: FunctionName -> (Name, [CVQualifier])
cleanFunctionName (FunctionName nm) =
  case nm of
    NameNested (NestedName p u cvq mbrq) ->
      (NameNested $ NestedName p u [] mbrq, cvq)
    NameNested (NestedTemplateName tp ta cvq mbrq) ->
      (NameNested $ NestedTemplateName tp ta [] mbrq, cvq)
    _ -> (nm, [])

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  , Sayable saytag (Encoding, Context)
  -- , Sayable saytag (CallOffset, Context)
  ) => Sayable saytag (SpecialName, Context) where
  sayable (n, c) =
    case n of
      VirtualTable ty -> t'"vtable for" &- (ty,c)
      TemplateParameterObj ta -> t'"template parameter object for" &- (ta,c)
      VTT ty -> t'"VTT for" &- (ty,c)
      TypeInfo ty -> t'"typeinfo for" &- (ty,c)
      TypeInfoName ty -> t'"typeinfo name for" &- (ty,c)
      CtorVTable _ -> t'"construction vtable for" &- t'"()"
      Thunk (VirtualOffset _o1 _o2) enc -> t'"virtual thunk to" &- (enc,c)
      Thunk (NonVirtualOffset _o1) enc -> t'"non-virtual thunk to" &- (enc,c)


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Name, Context)
  ) => Sayable saytag (FunctionName, Context) where
  sayable (FunctionName n, c) = sayable @saytag (n, c)


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (NestedName, Context)
  , Sayable saytag (TemplateArgs, Context)
  , Sayable saytag (FunctionScope, Context)
  , Sayable saytag (FunctionEntity, Context)
  , Sayable saytag (Discriminator, Context)
  ) => Sayable saytag (Name, Context) where
  sayable (n, c) =
    case n of
      NameNested nn -> sayable @saytag (nn,c)
      UnscopedName False uqn -> sayable @saytag (uqn,c)
      UnscopedName True uqn -> t'"std::" &+ (uqn,c)
      UnscopedTemplateName nn ta -> (nn,c) &+ (ta,c)
      LocalName fs fe mbd -> (fs,c) &+ t'"::" &+ (fe,c) &? ((,c) <$> mbd) -- ??
      StringLitName fs mbd -> (fs,c) &? ((,c) <$> mbd) -- ??


instance {-# OVERLAPPABLE #-} Sayable saytag (Coord, Context) where
  sayable (i, c) = sayable @saytag $ contextStr c i


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Operator, Context)
  , Sayable saytag (ABI_Tag, Context)
  , Sayable saytag (CtorDtor, Context)
  ) =>  Sayable saytag (UnqualifiedName, Context) where
  sayable (n, c) =
    case n of
      SourceName i -> sayable @saytag $ contextStr c i
      OperatorName op [] -> sayable @saytag (op, c)
      OperatorName op tags ->
        (op, c) &- t'"[[gnu::abi_tag (" &+ ctxLst tags c &+ t'")]]"
      CtorDtorName cd -> sayable @saytag (cd, c)
      StdSubst subs -> sayable @saytag (subs, c)

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Operator, Context)
  , Sayable saytag (ABI_Tag, Context)
  , Sayable saytag (CtorDtor, Context)
  ) =>  Sayable saytag (Prefix, UnqualifiedName, Context) where
  sayable (p, n, c) =
    case n of
      CtorDtorName cd -> sayable @saytag (p, cd, c)
      _ -> sayable @saytag (n, c)

{- | Use Sayable (Prefix, CtorDtor, Context) instead, since CtorDtor needs to
   reproduce Prefix name. -}
instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  ) =>  Sayable saytag (CtorDtor, Context) where
  sayable (n, c) =
    case n of
      CompleteCtor -> 'c' &+ '1'
      BaseCtor -> 'c' &+ '2'
      CompleteAllocatingCtor -> 'c' &+ '3'
      CompleteInheritingCtor t -> t'"ci1" &+ (t,c)
      BaseInheritingCtor t -> t'"ci2" &+ (t,c)
      DeletingDtor -> 'd' &+ '0'
      CompleteDtor -> 'd' &+ '1'
      BaseDtor -> 'd' &+ '2'

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  ) =>  Sayable saytag (Prefix, CtorDtor, Context) where
  sayable (p, n, c) =
    let mb'ln = case p of
                  Prefix pfxr -> pfxrLastUQName pfxr
                  _ -> cannot Demangler "sayable"
                       [ "CTORDTOR UNK PFX: " <> show p ]
        pfxrLastUQName = \case
          PrefixUQName unm PrefixEnd -> Just unm
          PrefixUQName unm (PrefixTemplateArgs _ PrefixEnd) -> Just unm
          PrefixUQName _ sp -> pfxrLastUQName sp
          PrefixTemplateArgs _ sp -> pfxrLastUQName sp
          PrefixEnd -> Nothing
    in case mb'ln of
         Just ln ->
           case n of
             CompleteCtor -> sayable @saytag (ln,c)
             BaseCtor -> sayable @saytag (ln,c)
             CompleteAllocatingCtor -> sayable @saytag (ln,c)
             CompleteInheritingCtor t -> sayable @saytag (t,c) -- ??
             BaseInheritingCtor t -> sayable @saytag (t,c) -- ??
             DeletingDtor -> '~' &+ (ln,c)
             CompleteDtor -> '~' &+ (ln,c)
             BaseDtor -> '~' &+ (ln,c)
         Nothing -> t'"unk_" &+ sayable @saytag (n, c) -- unlikely... and will be wrong


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (Type_, Context)
  ) =>  Sayable saytag (Operator, Context) where
  sayable (op, c) =
    case lookup op opTable of
      Just (_, o) -> t'"operator" &+ o
      Nothing ->
        case op of
          OpCast ty -> t'"operator" &- (ty, c)
          OpString uqnm -> sayable @saytag (uqnm, c)
          OpVendor n uqnm -> t'"vendor" &- n &- (uqnm, c)
          _ -> cannotSay Demangler "sayable"
               [ "Operator not in opTable or with a specific override:"
               , show op
               ]

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Prefix, Context)
  , Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (CVQualifier, Context)
  , Sayable saytag (RefQualifier, Context)
  , Sayable saytag (TemplatePrefix, Context)
  , Sayable saytag (TemplateArgs, Context)
  ) => Sayable saytag (NestedName, Context) where
  sayable (n, c) =
    let qualrefs q r = ctxLst' q c " " &? ((,c) <$> r)
    in case n of
      NestedName p (CtorDtorName nm) q r ->
        qualrefs q r &+ (p,c) &+ t'"::" &+ (p,nm,c)
      NestedName EmptyPrefix nm q r -> qualrefs q r &+ (nm,c)
      NestedName p nm q r -> qualrefs q r &+ (p,c) &+ t'"::" &+ (nm,c)
      NestedTemplateName tp ta q r -> qualrefs q r &+ (tp,c) &+ (ta,c)


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (ClosurePrefix, Context)
  , Sayable saytag (TemplateParam, Context)
  , Sayable saytag (DeclType, Context)
  , Sayable saytag (PrefixR, Context)
  ) => Sayable saytag (Prefix, Context) where
  sayable (p, c) =
    case p of
      PrefixTemplateParam tp prefixr -> (tp, c) &+ (prefixr, c)
      PrefixDeclType dt prefixr -> (dt, c) &+ (prefixr, c)
      PrefixClosure cp -> sayable @saytag (cp, c) -- ??
      Prefix prefixr -> sayable @saytag (prefixr, c)

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (TemplateArgs, Context)
  ) => Sayable saytag (PrefixR, Context) where
  sayable (p, c) =
    case p of
      PrefixUQName uqn pfr@(PrefixUQName {}) -> (uqn,c) &+ t'"::" &+ (pfr,c)
      PrefixUQName uqn pfr -> (uqn,c) &+ (pfr,c)
      PrefixTemplateArgs ta pfr -> (ta,c) &+ (pfr,c)
      PrefixEnd -> sayable @saytag $ t'""


instance {-# OVERLAPPABLE #-} Sayable saytag (CVQualifier, Context) where
  sayable (q, _c) =
    case q of
      Restrict -> sayable @saytag $ t'"restrict"
      Volatile -> sayable @saytag $ t'"volatile"
      Const_ -> sayable @saytag $ t'"const"

instance {-# OVERLAPPABLE #-} Sayable saytag (RefQualifier, Context) where
  sayable (q, _c) =
    case q of
      Ref -> sayable @saytag '&'
      RefRef -> sayable @saytag $ t'"&&"

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (Prefix, UnqualifiedName, Context)
  , Sayable saytag (TemplateParam, Context)
  ) => Sayable saytag (TemplatePrefix, Context) where
  sayable (p, c) =
    case p of
      GlobalTemplate uqns -> ctxLst' uqns c "::"
      NestedTemplate pr uqns -> (pr,c) &+ t'"::"
                                &+ t'"::" &:* ((\n -> (pr,n,c)) <$> uqns)
      TemplateTemplateParam tp -> sayable @saytag (tp, c)


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (TemplateArg, Context)
  ) => Sayable saytag (TemplateArgs, Context) where
  sayable (args, c) = '<' &+ ctxLst args c &+ templateArgsEnd args

-- C++ requires a space between template argument closures to resolve the parsing
-- ambiguity between that and a right shift operation.(e.g. "list<foo<int> >"
-- instead of "list<foo<int>>"
templateArgsEnd :: TemplateArgs -> String
templateArgsEnd args = case NEL.last args of
                        TArgPack targs ->
                          case NEL.nonEmpty targs of
                            Just args' -> templateArgsEnd args'
                            -- Expected to need ellipsis here, but c++filt does
                            -- not emit them.
                            -- Nothing -> "..."
                            Nothing -> ">"
                        TArgType (ClassUnionStructEnum
                                  (NameNested
                                   (NestedTemplateName {}))) -> " >"
                        TArgType (ClassUnionStructEnum
                                  (UnscopedTemplateName {})) -> " >"
                        _ -> ">"

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  , Sayable saytag (ExprPrimary, Context)
  , Sayable saytag (Expression, Context)
  , Sayable saytag (TemplateArgs, Context)
  ) => Sayable saytag (TemplateArg, Context) where
  sayable (p, c) =
    case p of
      TArgType ty -> sayable @saytag (ty, c)
      TArgSimpleExpr ep -> sayable @saytag (ep, c)
      TArgExpr expr -> sayable @saytag (expr, c)
      TArgPack tas ->
        -- Expected some ellipses (see
        -- https://en.cppreference.com/w/cpp/language/parameter-pack), but
        -- c++filt does not show them in that manner.
        --
        -- if null tas  then '.' &+ ".."
        -- else (NEL.fromList tas, c) &+ "..."
        --
        -- Do not simply defer to the TemplateArgs sayable because that will
        -- engender another pair of surrounding angle brackets.
        ctxLst tas c

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (ExprPrimary, Context)
  , Sayable saytag (TemplateParam, Context)
  ) => Sayable saytag (Expression, Context) where
  sayable (e, c) =
    case e of
      ExprPack expr -> sayable @saytag (expr, c)
      ExprTemplateParam tp -> sayable @saytag (tp, c)
      ExprPrim pe -> sayable @saytag (pe, c)


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  , Sayable saytag (Encoding, Context)
  ) => Sayable saytag (ExprPrimary, Context) where
  sayable (e, c) =
    case e of
      IntLit ty n ->
        -- Normally these are printed with a typecast (e.g. `(type)`) ".
        -- However, C and C++ have some special situations where they can use
        -- special suffixes instead (e.g. `10ul` for unsigned long).  And some
        -- are just wholesale changes.
        case ty of
          BaseType Bool_ -> t'"" &+ if n > 0 then t'"true" else t'"false"
          BaseType bty -> case lookup bty builtinTypeTable of
                            Just (_, cst, sfx) -> if T.null sfx
                                                  then '(' &+ cst &+ ')' &+ n
                                                  else n &+ sfx
                            _ -> '(' &+ (ty, c) &+ ')' &+ n
          _ -> '(' &+ (ty, c) &+ ')' &+ n
      FloatLit ty n -> '(' &+ (ty, c) &+ ')' &+ n
      ComplexFloatLit ty r i -> '(' &+ (ty, c) &+ ')' &+ '(' &+ r &+ ',' &- i &+ ')'
      DirectLit ty -> '(' &+ (ty, c) &+ t'")NULL"  -- except String?
      NullPtrTemplateArg ty -> '(' &+ (ty, c) &+ t'")0"
      ExternalNameLit enc -> sayable @saytag (enc, c)


instance {-# OVERLAPPABLE #-} Sayable saytag (ClosurePrefix, Context) where
  sayable (_p, _c) = cannotSay Demangler "sayable"
                     [ "No Sayable for ClosurePrefix" ]

-- instance {-# OVERLAPPABLE #-} Sayable saytag (TemplateParam, Context) where
--   sayable (p, _c) = undefined

-- instance {-# OVERLAPPABLE #-} Sayable saytag (DeclType, Context) where
--   sayable (p, _c) = undefined

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (StdType, Context)
  ) => Sayable saytag (Substitution, Context) where
  sayable (p, c) =
    case p of
      SubStd -> t'"std" &+ t'""
      SubAlloc -> t'"std" &+ t'"::allocator"
      SubBasicString -> t'"std" &+ t'"::basic_string"
      SubStdType stdTy -> sayable @saytag (stdTy, c)

instance {-# OVERLAPPABLE #-} Sayable saytag (StdType, Context) where
  sayable (stdTy, _c) =
    let ct = t'"std::char_traits<char>" in
    case stdTy of
      BasicStringChar -> t'"std::basic_string<char," &- ct &+ t'", std::allocator<char> >"
      BasicIStream -> t'"std::basic_istream<char," &- ct &- '>'
      BasicOStream -> t'"std::basic_ostream<char," &- ct &- '>'
      BasicIOStream -> t'"std::basic_iostream<char," &- ct &- '>'

-- instance {-# OVERLAPPABLE #-} Sayable saytag (ExtendedQualifier, Context) where
--   sayable (p, _c) = undefined

instance {-# OVERLAPPABLE #-} Sayable saytag (ABI_Tag, Context) where
  sayable (ABITag p, c) = '"' &+ (p, c) &+ '"'

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (BaseType, Context)
  , Sayable saytag (Name, Context)
  , Sayable saytag (CVQualifier, Context)
  , Sayable saytag (ExtendedQualifier, Context)
  , Sayable saytag (ExceptionSpec, Context)
  , Sayable saytag (Transaction, Context)
 ) => Sayable saytag (Type_, Context) where
  sayable (ty, c) =
    case ty of
      BaseType t -> sayable @saytag (t,c)
      QualifiedType [] [] t -> sayable @saytag (t,c)
      QualifiedType eqs [] t -> (t,c) &+ ctxLst' eqs c " "
      QualifiedType [] cvqs t -> (t,c) &- ctxLst' cvqs c " "
      QualifiedType eqs cvqs t -> (t,c) &- ctxLst' eqs c " " &- ctxLst' cvqs c " "
      ClassUnionStructEnum n -> sayable @saytag (n,c)
      ClassStruct n -> sayable @saytag (n,c)
      Union n -> sayable @saytag (n,c)
      Enum n -> sayable @saytag (n,c)
      Function {} -> sayFunctionType ty "" c
      Pointer f@(Function {}) -> sayFunctionType f "(*)" c
      Pointer t -> (t,c) &+ '*'
      LValRef t -> (t,c) &+ '&'
      RValRef t -> (t,c) &+ t'"&&"
      ComplexPair t -> (t,c) &- t'"complex"
      Imaginary t -> (t,c) &- t'"imaginary"
      Template tp ta -> (tp,c) &- (ta,c) -- ??
      Cpp11PackExpansion ts ->
        -- XXX expected some "..." (see
        -- https://en.cppreference.com/w/cpp/language/parameter-pack) but c++filt
        -- does not visibly decorate these.
        t'"" &+* ((,c) <$> ts)
      StdType stdTy -> sayable @saytag (stdTy, c)

sayFunctionType :: Type_ -> Text -> Context -> Saying saytag
sayFunctionType (Function cvqs mb'exc trns isExternC rTy argTys mb'ref) nm c =
  ctxLst' cvqs c " "
  &? ((,c) <$> mb'exc)
  &+ (trns, c)
  &+ (if isExternC then t'" extern \"C\"" else t'"")
  &+ (rTy, c)
  &- nm &+ '('
  &+* (case argTys of
          BaseType Void :| [] -> []
          _ -> (,c) <$> NEL.toList argTys
      )
  &+ ')'
  &? ((,c) <$> mb'ref)
sayFunctionType _ _ _ = cannotSay Demangler "sayFunctionType"
                        [ "Called with a type that is not a Function!" ]


instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Expression, Context)
  , Sayable saytag (Type_, Context)
  ) => Sayable saytag (ExceptionSpec, Context) where
  sayable (exc, c) =
    case exc of
      NonThrowing -> sayable @saytag $ t'"noexcept"
      ComputedThrow expr -> t'"throw" &- (expr, c) -- ?
      Throwing tys -> t'"throw (" &+* ((,c) <$> tys) &+ ')' -- ?

instance {-# OVERLAPPABLE #-} Sayable saytag (Transaction, Context) where
  sayable (trns, _c) =
    case trns of
      TransactionSafe -> sayable @saytag $ t'"safe" -- ?
      TransactionUnsafe -> sayable @saytag $ t'""

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (TemplateArgs, Context)
  ) => Sayable saytag (BaseType, Context) where
  sayable (t, c) =
    case lookup t builtinTypeTable of
      Just (_,s,_) -> sayable @saytag s
      Nothing ->
        case t of
          FloatN n -> t'"std::float" &+ n &+ t'"_t"
          FloatNx n -> t'"std::float" &+ n &+ t'"x_t"
          SBitInt n -> t'"signed _BitInt(" &+ n &+ ')'
          UBitInt n -> t'"unsigned _BitInt(" &+ n &+ ')'
          VendorExtendedType nm mb'ta -> (nm,c) &? ((,c) <$> mb'ta)
          _ -> cannotSay Demangler "sayable.Basetype"
               [ "Unknown BaseType not listed in the builtinTypeTable"
               , show t
               ]

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (Type_, Context)
  , Sayable saytag (UnqualifiedName, Context)
  , Sayable saytag (Prefix, Context)
  , Sayable saytag (TemplatePrefix, Context)
  , Sayable saytag (TemplateArg, Context)
  ) => Sayable saytag (SubsCandidate, Context) where
  sayable (cand, c) = -- For debug only
    case cand of
      SC_Type t -> t'"SC_Ty" &- (t, c)
      SC_UQName True n -> t'"SC_UN" &- t'"std::" &+ (n, c)
      SC_UQName _ n -> t'"SC_UN" &- (n, c)
      SC_Prefix p -> t'"SC_PR" &- (p, c)
      SC_TemplatePrefix tp -> t'"SC_TP" &- (tp, c)
