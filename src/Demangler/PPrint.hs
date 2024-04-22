{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-- OPTIONS_GHC -ddump-splices #-}

module Demangler.PPrint () where

import           Control.Applicative
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
import           Panic

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


data PrefixUQN = PUC Prefix UnqualifiedName
data PrefixCDtor = PCDC Prefix CtorDtor

$(return [])

ctxLst :: forall saytag t a b .
          Sayable saytag (WithContext a)
       => Functor t
       => Foldable t
       => t a -> WithContext b -> Saying saytag
ctxLst l wc = t'"" &+* wCtx l wc

ctxLst' :: Sayable saytag (WithContext a)
        => Functor t
        => Foldable t
        => t a -> WithContext b -> Text -> Saying saytag
ctxLst' l wc sep = sep &:* wCtx l wc

wCtx :: Functor t => t a -> WithContext b -> t (WithContext a)
wCtx a wc = withContext wc <$> a


----------------------------------------------------------------------
-- Sayable instances for printing demangled results

instance {-# OVERLAPPING #-}
  ( Sayable "diagnostic" (WithContext Encoding)
  ) => Sayable "diagnostic" Result where
  sayable = \case
    (Original i, c) -> contextStr (addContext () c) i &- t'"{orig}"
    (Encoded e, c) -> sayable @"diagnostic" $ addContext e c
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr (addContext () c) i
      in addContext d c &- t'"[clone" &- s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (WithContext Encoding)
  ) => Sayable saytag Result where
  sayable = \case
    (Original i, c) -> sayable @saytag $ contextStr (addContext () c) i
    (Encoded e, c) -> sayable @saytag $ addContext e c
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr (addContext () c) i
      in addContext d c &- t'"[clone" &- '.' &+ s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Encoding
  ) => Sayable saytag (WithContext Encoding) where
  sayable wc =
    case contextData wc of
      -- Note: if the function has only a single void argument, print "()"
      -- instead of "(void)"; these are semantically the same, but demangling
      -- emits the former.
      --
      -- Another tricky part is that the FunctionName may contain qualifiers
      -- (esp. "const") but for a function these must be placed at the end,
      -- following the arguments.
      --
      -- Additionally, if this function is being printed as part of a template
      -- argument, then do not print the arguments.  This conforms to GCC c++filt
      -- output, although llvm-cxxfilt *does* print the arguments, however, the
      -- testing oracle is c++filt.
      EncFunc f rty (BaseType Void :| []) -> sayFunction wc f rty []
      EncFunc f rty t -> sayFunction wc f rty $ NEL.toList t
      -- n.b. static functions don't have any visible difference in demangled
      -- form.
      EncStaticFunc f rty (BaseType Void :| []) -> sayFunction wc f rty []
      EncStaticFunc f rty t -> sayFunction wc f rty $ NEL.toList t
      EncConstStructData nm -> sayable @saytag $ withContext wc nm
      EncData nm -> sayable @saytag $ withContext wc nm
      EncSpecial sn -> sayable @saytag $ withContext wc sn

sayFunction :: Sayable saytag (WithContext Type_)
            => WithContext a -> FunctionName -> Maybe Type_ -> [Type_] -> Saying saytag
sayFunction wc fn mbRet args =
  let (nm,q) = cleanFunctionName fn
      part1 = case mbRet of
                Nothing -> withContext wc nm &+ t'""
                Just rty -> withContext wc rty &- withContext wc nm
      part2 = if isTemplateArgContext wc
              then part1
              else part1 &+ '(' &+ ctxLst args wc &+ ')'
  in if null q then part2 else part2 &- ctxLst' q wc " "

instance Sayable saytag (WithContext a)
  => Sayable saytag (NonEmpty (WithContext a)) where
  sayable l = t'"" &+* l

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext a)
  => Sayable saytag (WithContext (NonEmpty a)) where
  sayable wc = ctxLst (contextData wc) wc

cleanFunctionName :: FunctionName -> (Name, [CVQualifier])
cleanFunctionName (FunctionName nm) =
  case nm of
    NameNested (NestedName p u cvq mbrq) ->
      (NameNested $ NestedName p u [] mbrq, cvq)
    NameNested (NestedTemplateName tp ta cvq mbrq) ->
      (NameNested $ NestedTemplateName tp ta [] mbrq, cvq)
    _ -> (nm, [])

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''SpecialName
  ) => Sayable saytag (WithContext SpecialName) where
  sayable wc =
    case contextData wc of
      VirtualTable ty -> t'"vtable for" &- withContext wc ty
      TemplateParameterObj ta -> t'"template parameter object for" &- withContext wc ta
      VTT ty -> t'"VTT for" &- withContext wc ty
      TypeInfo ty -> t'"typeinfo for" &- withContext wc ty
      TypeInfoName ty -> t'"typeinfo name for" &- withContext wc ty
      CtorVTable _ -> t'"construction vtable for" &- t'"()"
      Thunk (VirtualOffset _o1 _o2) enc -> t'"virtual thunk to" &- withContext wc enc
      Thunk (NonVirtualOffset _o1) enc -> t'"non-virtual thunk to" &- withContext wc enc


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''FunctionName
  ) => Sayable saytag (WithContext FunctionName) where
  sayable wc = let FunctionName n = contextData wc
               in sayable @saytag $ withContext wc n


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Name
  ) => Sayable saytag (WithContext Name) where
  sayable wc =
    case contextData wc of
      NameNested nn -> sayable @saytag $ withContext wc nn
      UnscopedName False uqn -> sayable @saytag $ withContext wc uqn
      UnscopedName True uqn -> t'"std::" &+ withContext wc uqn
      UnscopedTemplateName nn ta -> withContext wc nn &+ withContext wc ta
      LocalName fs fe _discr -> withContext wc fs &+ t'"::" &+ withContext wc fe -- Discriminators are invisible in demangled form
      StringLitName fs _discr -> sayable @saytag $ withContext wc fs  -- Discriminators are invisible in demangled form


-- Note: this should never actually be used, but the sayableConstraints template
-- haskell production doesn't know that.
instance Sayable saytag Discriminator where
  sayable _ = sayable @saytag $ t'""
instance Sayable saytag (WithContext Discriminator) where
  sayable _ = sayable @saytag $ t'""


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext Coord) where
  sayable wc = sayable @saytag $ contextStr wc $ contextData wc


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''UnqualifiedName
  ) =>  Sayable saytag (WithContext UnqualifiedName) where
  sayable wc =
    case contextData wc of
      SourceName i [] -> sayable @saytag $ withContext wc i
      SourceName i tags -> withContext wc i &+ ctxLst' tags wc ""
      OperatorName op [] -> t'"operator" &+ withContext wc op
      OperatorName op tags -> t'"operator" &+ withContext wc op &+ ctxLst' tags wc ""
      CtorDtorName cd -> sayable @saytag $ withContext wc cd
      StdSubst subs -> sayable @saytag $ withContext wc subs
      ModuleNamed mn uqn -> ctxLst' mn wc "" &+ withContext wc uqn
      -- GCC c++filt style:
      UnnamedTypeName Nothing -> t'"{unnamed type#1" &+ '}'
      UnnamedTypeName (Just nt) -> t'"{unnamed type#" &+ nt + 2 &+ '}'
      -- llvm-cxxfilt style:
      -- UnnamedTypeName Nothing -> t'"'unnamed" &+ '\''
      -- UnnamedTypeName (Just nt) -> t'"'unnamed" &+ nt &+ '\''


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''SourceName
   ) => Sayable saytag (WithContext SourceName) where
  sayable wc = let SrcName i = contextData wc in sayable @saytag $ contextStr wc i


instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''PrefixUQN)
  , Sayable saytag (WithContext PrefixCDtor)
  ) =>  Sayable saytag (WithContext PrefixUQN) where
  sayable wc =
    let PUC p n = contextData wc in
    case n of
      CtorDtorName cd -> sayable @saytag $ withContext wc (PCDC p cd)
      _ -> sayable @saytag $ withContext wc n

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ModuleName
  ) => Sayable saytag (WithContext ModuleName) where
  sayable wc =
    let ModuleName isP sn = contextData wc
    in if isP then withContext wc sn &+ ':' else withContext wc sn &+ '.'

{- | Use Sayable (Prefix, CtorDtor, Context) instead, since CtorDtor needs to
   reproduce Prefix name. -}
instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''CtorDtor
   ) =>  Sayable saytag (WithContext CtorDtor) where
  sayable wc =
    case contextData wc of
      CompleteCtor -> '(' &+ ')'
      BaseCtor -> '(' &+ ')'
      CompleteAllocatingCtor -> '(' &+ ')'
      CompleteInheritingCtor t -> withContext wc t &+ '(' &+ ')' -- ?
      BaseInheritingCtor t -> withContext wc t &+ '(' &+ ')' -- ?
      DeletingDtor -> '~' &+ '(' &+ ')'
      CompleteDtor -> '~' &+ '(' &+ ')'
      BaseDtor -> '~' &+ '(' &+ ')'

instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''PrefixCDtor)
  ) =>  Sayable saytag (WithContext PrefixCDtor) where
  sayable wc =
    let PCDC p n = contextData wc
        mb'ln = case p of
                  Prefix pfxr -> pfxrLastUQName pfxr
                  _ -> cannot Demangler "sayable"
                       [ "CTORDTOR UNK PFX: " <> show p ]
        pfxrLastUQName = \case
          PrefixUQName (UnnamedTypeName _) PrefixEnd -> Nothing
          PrefixUQName (UnnamedTypeName _) (PrefixTemplateArgs _ PrefixEnd) -> Nothing
          PrefixUQName unm PrefixEnd -> Just unm
          PrefixUQName unm (PrefixTemplateArgs _ PrefixEnd) -> Just unm
          PrefixUQName unm sp -> pfxrLastUQName sp <|> Just unm  -- [note UTC]
          PrefixTemplateArgs _ sp -> pfxrLastUQName sp
          PrefixEnd -> Nothing
    in case mb'ln of
         Just ln ->
           case n of
             CompleteCtor -> sayable @saytag $ withContext wc ln
             BaseCtor -> sayable @saytag $ withContext wc ln
             CompleteAllocatingCtor -> sayable @saytag $ withContext wc ln
             CompleteInheritingCtor t -> sayable @saytag $ withContext wc t -- ??
             BaseInheritingCtor t -> sayable @saytag $ withContext wc t -- ??
             DeletingDtor -> '~' &+ withContext wc ln
             CompleteDtor -> '~' &+ withContext wc ln
             BaseDtor -> '~' &+ withContext wc ln
         Nothing -> sayable @saytag $ withContext wc n

-- [Note UTC:] When printing a constructor or destructor that includes an
-- UnnamedTypeName, there are differences between GCC's c++filt and LLVM's
-- llvm-cxxfilt.  We adopt the former because the demangle tests use c++filt as
-- an oracle, but it is possible to switch to the LLVM style (at compile time) by
-- removing the alternative return of Just unm from the indicated
--
-- Example:
--    _ZN3FooUt3_C2Ev is the base constructor for the 5th unnamed type
--    in the Foo namespace.
--
--      c++filt _ZN3FooUt3_C2Ev -------> Foo::{unnamed type#5}::Foo()
--      llvm-cxxfilt _ZN3FooUt3_C2Ev --> Foo::'unnamed3'::()'


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Operator
  ) =>  Sayable saytag (WithContext Operator) where
  sayable wc =
    let op = contextData wc in
    case lookup op opTable of
      Just (_, (_, o)) -> sayable @saytag o
      Nothing ->
        -- TODO: if these are printed as part of an expression rather than an
        -- UnqualifiedName, the prefix space will be wrong (the latter prints
        -- "operator" to name the function whereas the former just prints the
        -- operation).  If this is an issue, probably needs to be a flag in
        -- WithContext to indicate if this is an expression or not.
        case op of
          OpCast ty -> ' ' &+ withContext wc ty
          OpString snm -> ' ' &+ withContext wc snm
          OpVendor n snm -> t'"vendor" &- n &- withContext wc snm  -- ?
          _ -> cannotSay Demangler "sayable"
               [ "Operator not in opTable or with a specific override:"
               , show op
               ]

instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''NestedName)
  , Sayable saytag (WithContext PrefixCDtor)
  ) => Sayable saytag (WithContext NestedName) where
  sayable wc =
    let qualrefs q r = ctxLst' q wc " " &? wCtx r wc
    in case contextData wc of
      NestedName p (CtorDtorName nm) q r ->
        qualrefs q r &+ withContext wc p &+ t'"::" &+ withContext wc (PCDC p nm)
      NestedName EmptyPrefix nm q r -> qualrefs q r &+ withContext wc nm
      NestedName p nm q r -> qualrefs q r &+ withContext wc p &+ t'"::" &+ withContext wc nm
      NestedTemplateName tp ta q r -> qualrefs q r &+ withContext wc tp &+ withContext wc ta


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Prefix
  ) => Sayable saytag (WithContext Prefix) where
  sayable wc =
    case contextData wc of
      PrefixTemplateParam tp prefixr -> withContext wc tp &+ withContext wc prefixr
      PrefixDeclType dt prefixr -> withContext wc dt &+ withContext wc prefixr
      PrefixClosure cp -> sayable @saytag $ withContext wc cp -- ??
      Prefix prefixr -> sayable @saytag $ withContext wc prefixr


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''PrefixR
  ) => Sayable saytag (WithContext PrefixR) where
  sayable wc =
    case contextData wc of
      PrefixUQName uqn pfr@(PrefixUQName {}) -> withContext wc uqn &+ t'"::" &+ withContext wc pfr
      PrefixUQName uqn pfr -> withContext wc uqn &+ withContext wc pfr
      PrefixTemplateArgs ta pfr -> withContext wc ta &+ withContext wc pfr
      PrefixEnd -> sayable @saytag $ t'""


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext CVQualifier) where
  sayable wc =
    case contextData wc of
      Restrict -> sayable @saytag $ t'"restrict"
      Volatile -> sayable @saytag $ t'"volatile"
      Const_ -> sayable @saytag $ t'"const"

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext RefQualifier) where
  sayable wc =
    case contextData wc of
      Ref -> sayable @saytag '&'
      RefRef -> sayable @saytag $ t'"&&"

instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''TemplatePrefix)
  , Sayable saytag (WithContext PrefixUQN)
  ) => Sayable saytag (WithContext TemplatePrefix) where
  sayable wc =
    case contextData wc of
      GlobalTemplate uqns -> ctxLst' uqns wc "::"
      NestedTemplate pr uqns -> withContext wc pr &+ t'"::"
                                &+ ctxLst' (PUC pr <$> uqns) wc "::"
      TemplateTemplateParam tp -> sayable @saytag $ withContext wc tp


instance {-# OVERLAPPABLE #-}
  (Sayable saytag (WithContext TemplateArg)
  ) => Sayable saytag (WithContext TemplateArgs) where
  sayable wc = let args = contextData wc
               in '<' &+ ctxLst args wc &+ templateArgsEnd args

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
  ($(sayableConstraints ''TemplateArg)
  ) => Sayable saytag (WithContext TemplateArg) where
  sayable wc =
    case contextData wc of
      TArgType ty -> sayable @saytag $ withContextForTemplateArg wc ty
      TArgSimpleExpr ep -> sayable @saytag $ withContextForTemplateArg wc ep
      TArgExpr expr -> sayable @saytag $ withContextForTemplateArg wc expr
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
        ctxLst tas $ withContextForTemplateArg wc ()

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Expression
  ) => Sayable saytag (WithContext Expression) where
  sayable wc =
    case contextData wc of
      ExprUnary op expr -> withContext wc op &+ withContext wc expr
      ExprBinary op expr1 expr2 -> withContext wc expr1 &+ withContext wc op &+ withContext wc expr2
      ExprTrinary op expr1 expr2 expr3 ->
        '(' &+ withContext wc expr1 &+ ')' &+ withContext wc op &+ withContext wc expr2 &- ':' &- withContext wc expr3
      ExprPfxPlus expr -> t'"++" &+ withContext wc expr
      ExprPfxMinus expr -> t'"--" &+ withContext wc expr
      ExprCall (exprc :| args) -> withContext wc exprc &+ '(' &+ ctxLst args wc &+ ')'
      ExprConvert1 ty expr -> '(' &+ withContext wc ty &+ ')' &+ withContext wc expr
      ExprConvertSome ty exprs -> '(' &+ withContext wc ty &+ t'")(" &+ ctxLst exprs wc &+ ')'
      ExprConvertInit ty brexprs -> withContext wc ty &+ '{' &+ ctxLst brexprs wc &+ '}'
      ExprBracedInit brexprs -> '{' &+ ctxLst brexprs wc &+ '}'
      ExprNew gs exprs ty -> t'"new (" &+ ctxLst exprs wc &+ ')'
                             &- (if gs then "::" else t'"") &+ withContext wc ty
      ExprNewInit gs exprs ty i -> t'"new (" &+ ctxLst exprs wc &+ ')'
                                   &- (if gs then "::" else t'"") &+ withContext wc ty
                                   &- '(' &+ withContext wc i &+ ')'
      ExprNewArray gs exprs ty -> t'"new[] (" &+ ctxLst exprs wc &+ ')'
                                  &- (if gs then "::" else t'"") &+ withContext wc ty
      ExprNewInitArray gs exprs ty i -> t'"new[] (" &+ ctxLst exprs wc &+ ')'
                                        &- (if gs then "::" else t'"") &+ withContext wc ty
                                        &- '(' &+ withContext wc i &+ ')'
      ExprDel gs expr -> t'"delete" &- (if gs then "::" else t'"") -- ??
                         &+ withContext wc expr
      ExprDelArray gs expr -> t'"delete[]" &- (if gs then "::" else t'"") -- ??
                              &+ withContext wc expr
      ExprDynamicCast ty expr -> t'"dynamic_cast<" &+ withContext wc ty &+ t'">("
                                 &+ withContext wc expr &+ ')'
      ExprStaticCast ty expr -> t'"static_cast<" &+ withContext wc ty &+ t'">("
                                &+ withContext wc expr &+ ')'
      ExprConstCast ty expr -> t'"const_cast<" &+ withContext wc ty &+ t'">("
                               &+ withContext wc expr &+ ')'
      ExprReinterpretCast ty expr -> t'"reinterpret_cast<" &+ withContext wc ty &+ t'">("
                                     &+ withContext wc expr &+ ')'
      ExprTypeIdType ty -> t'"typeid(" &+ withContext wc ty &+ ')'
      ExprTypeId expr -> t'"typeid(" &+ withContext wc expr &+ ')'
      ExprSizeOfType ty -> t'"sizeof(" &+ withContext wc ty &+ ')'
      ExprSizeOf expr -> t'"sizeof(" &+ withContext wc expr &+ ')'
      ExprAlignOfType ty -> t'"alignof(" &+ withContext wc ty &+ ')'
      ExprAlignOf expr -> t'"alignof(" &+ withContext wc expr &+ ')'
      ExprNoException expr -> t'"noexcept(" &+ withContext wc expr &+ ')'
      ExprTemplateParam tp -> sayable @saytag $ withContext wc tp
      ExprFunctionParam fp -> sayable @saytag $ withContext wc fp
      ExprField expr urn -> withContext wc expr &+ '.' &+ withContext wc urn
      ExprFieldPtr expr urn -> withContext wc expr &+ t'"->" &+ withContext wc urn
      ExprFieldExpr baseExp fieldExp -> withContext wc baseExp &+ t'".*" &+ withContext wc fieldExp
      ExprSizeOfTmplParamPack tp -> t'"sizeof...(" &+ withContext wc tp &+ ')'
      ExprSizeOfFuncParamPack fp -> t'"sizeof...(" &+ withContext wc fp &+ ')'
      ExprSizeOfCapturedTmplParamPack tas -> t'"sizeof...(" &+ ctxLst tas wc &+ ')'
      ExprPack expr -> withContext wc expr &+ t'"..."
      ExprUnaryLeftFold op expr  -> '(' &+ t'"..." &- withContext wc op &- withContext wc expr &+ ')'
      ExprUnaryRightFold op expr -> '(' &+ withContext wc expr &- withContext wc op &- t'"..." &+ ')'
      ExprBinaryLeftFold op exprL exprR  ->
        '(' &+ withContext wc exprL &- withContext wc op &- t'"..." &- withContext wc op &- withContext wc exprR &+ ')'
      ExprBinaryRightFold op exprL exprR ->
        '(' &+ withContext wc exprL &- withContext wc op &- t'"..." &- withContext wc op &- withContext wc exprR &+ ')'
      ExprThrow expr -> t'"throw" &- withContext wc expr
      ExprReThrow -> sayable @saytag $ t'"throw"
      ExprVendorExtended sn tas -> withContext wc sn &+ '<' &+ ctxLst tas wc &+ '>'
      ExprUnresolvedName urn -> sayable @saytag $ withContext wc urn
      ExprPrim pe -> sayable @saytag $ withContext wc pe

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ExprPrimary
  ) => Sayable saytag (WithContext ExprPrimary) where
  sayable wc =
    case contextData wc of
      IntLit ty n ->
        -- Normally these are printed with a typecast (e.g. `(type)`) ".
        -- However, C and C++ have some special situations where they can use
        -- special suffixes instead (e.g. `10ul` for unsigned long).  And some
        -- are just wholesale changes.
        case ty of
          BaseType Bool_ -> t'"" &+ if n > 0 then t'"true" else t'"false"
          BaseType bty -> case lookup bty builtinTypeTable of
                            Just (_, _, Just sfx) -> n &+ sfx
                            Just (_, cst, Nothing) -> '(' &+ cst &+ ')' &+ n
                            _ -> '(' &+ withContext wc ty &+ ')' &+ n
          _ -> '(' &+ withContext wc ty &+ ')' &+ n
      FloatLit ty n -> '(' &+ withContext wc ty &+ ')' &+ n
      ComplexFloatLit ty r i -> '(' &+ withContext wc ty &+ ')' &+ '(' &+ r &+ ',' &- i &+ ')'
      DirectLit ty -> '(' &+ withContext wc ty &+ t'")NULL"  -- except String?
      NullPtrTemplateArg ty -> '(' &+ withContext wc ty &+ t'")0"
      ExternalNameLit enc -> sayable @saytag $ withContext wc enc


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''BracedExpression
   ) => Sayable saytag (WithContext BracedExpression) where
  sayable wc =
    case contextData wc of
      BracedExpr e -> sayable @saytag $ withContext wc e
      BracedFieldExpr sn be' -> '.' &+ withContext wc sn &+ withContext wc be'
      BracedIndexExpr ixe be' ->
        '[' &+ withContext wc ixe &+ ']' &+ '=' &+ '(' &+ withContext wc be' &+ ')'
      BracedRangedExpr sr er be' -> '[' &+ withContext wc sr &- t'"..." &- withContext wc er &+ ']'
                                    &- '=' &- withContext wc be'


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''InitializerExpr
   ) => Sayable saytag (WithContext InitializerExpr) where
  sayable wc = let Initializer ies = contextData wc in ctxLst ies wc


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''FunctionParam
   ) => Sayable saytag (WithContext FunctionParam) where
  sayable wc =
    case contextData wc of
      FP_This -> sayable @saytag $ t'"this"
      FP_ cvq n -> sayable @saytag $ '{' &+ ctxLst' cvq wc " " &+ t'"parm#" &+ n &+ '}'


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''UnresolvedName
   ) => Sayable saytag (WithContext UnresolvedName) where
  sayable wc =
    case contextData wc of
      URN_Base True burn -> t'"::" &+ withContext wc burn
      URN_Base False burn -> sayable @saytag $ withContext wc burn
      URNScopedRef urt burn -> withContext wc urt &+ t'"::" &+ withContext wc burn
      URNSubScopedRef urt urqls burn -> withContext wc urt &+ t'"::"
                                        &+ ctxLst' urqls wc (t'"::")
                                        &+ t'"::" &+ withContext wc burn
      URNQualRef True urqls burn -> t'"::"
                                    &+ ctxLst' urqls wc (t'"::")
                                    &+ t'"::" &+ withContext wc burn
      URNQualRef False urqls burn -> ctxLst' urqls wc (t'"::")
                                     &+ t'"::" &+ withContext wc burn


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''BaseUnresolvedName
   ) => Sayable saytag (WithContext BaseUnresolvedName) where
  sayable wc =
    case contextData wc of
      BUName sn Nothing -> sayable @saytag $ withContext wc sn
      BUName sn (Just targs) -> withContext wc sn &+ withContext wc targs
      BUOnOperator op -> sayable @saytag $ withContext wc op
      BUOnOperatorT op targs -> withContext wc op &+ withContext wc targs -- ?
      BUDestructorUnresolvedType urt -> '~' &+ withContext wc urt
      BUDestructorSimpleId sn Nothing -> '~' &+ withContext wc sn
      BUDestructorSimpleId sn (Just targs) -> '~' &+ withContext wc sn &+ withContext wc targs


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''UnresolvedType
   ) => Sayable saytag (WithContext UnresolvedType) where
  sayable wc =
    case contextData wc of
      URTTemplate tp Nothing -> sayable @saytag $ withContext wc tp
      URTTemplate tp (Just targs) -> withContext wc tp &+ withContext wc targs
      URTDeclType dt -> sayable @saytag $ withContext wc dt
      URTSubstPrefix pfx -> sayable @saytag $ withContext wc pfx


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''UnresolvedQualifierLevel
   ) => Sayable saytag (WithContext UnresolvedQualifierLevel) where
  sayable wc =
    case contextData wc of
      URQL sn Nothing -> sayable @saytag $ withContext wc sn
      URQL sn (Just targs) -> withContext wc sn &+ withContext wc targs


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''DeclType
   ) => Sayable saytag (WithContext DeclType) where
  sayable wc =
    case contextData wc of
      DeclType expr -> t'"decltype (" &+ withContext wc expr &+ ')'
      DeclTypeExpr expr -> t'"decltype (" &+ withContext wc expr &+ ')'


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext ClosurePrefix) where
  sayable _ = cannotSay Demangler "sayable"
              [ "No Sayable for ClosurePrefix" ]

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Substitution
  ) => Sayable saytag (WithContext Substitution) where
  sayable wc =
    case contextData wc of
      SubStd -> t'"std" &+ t'""
      SubAlloc -> t'"std" &+ t'"::allocator"
      SubBasicString -> t'"std" &+ t'"::basic_string"
      SubStdType stdTy -> sayable @saytag $ withContext wc stdTy

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext StdType) where
  sayable wc =
    let ct = t'"std::char_traits<char>" in
    case contextData wc of
      BasicStringChar -> t'"std::basic_string<char," &- ct &+ t'", std::allocator<char> >"
      BasicIStream -> t'"std::basic_istream<char," &- ct &- '>'
      BasicOStream -> t'"std::basic_ostream<char," &- ct &- '>'
      BasicIOStream -> t'"std::basic_iostream<char," &- ct &- '>'


-- n.b. LLVM and GNU syntax seems to be [abi:foo][abi:bar], despite the website
-- documentation of [[gnu::abi_tag ("foo", "bar")]]
instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ABI_Tag
  ) => Sayable saytag (WithContext ABI_Tag) where
  sayable wc = let ABITag p = contextData wc in t'"[abi:" &+ withContext wc p &+ ']'

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Type_
 ) => Sayable saytag (WithContext Type_) where
  sayable wc =
    case contextData wc of
      BaseType t -> sayable @saytag $ withContext wc t
      QualifiedType [] [] t -> sayable @saytag $ withContext wc t
      QualifiedType eqs [] t -> withContext wc t &+ ctxLst' eqs wc " "
      QualifiedType [] cvqs t -> withContext wc t &- ctxLst' cvqs wc " "
      QualifiedType eqs cvqs t -> withContext wc t &- ctxLst' eqs wc " " &- ctxLst' cvqs wc " "
      ClassUnionStructEnum n -> sayable @saytag $ withContext wc n
      ClassStruct n -> sayable @saytag $ withContext wc n
      Union n -> sayable @saytag $ withContext wc n
      Enum n -> sayable @saytag $ withContext wc n
      ty@(Function {}) -> sayFunctionType ty "" wc
      Pointer f@(Function {}) -> sayFunctionType f "(*)" wc
      Pointer (ArrayType bnd t) -> withContext wc t &- t'"(*)" &- '[' &+ withContext wc bnd &+ ']'
      Pointer t -> withContext wc t &+ '*'
      LValRef (ArrayType bnd t) -> withContext wc t &- t'"(&)" &- '[' &+ withContext wc bnd &+ ']'
      LValRef t -> withContext wc t &+ '&'
      RValRef (LValRef t@(QualifiedType _ [Const_] _)) ->
        -- An rvalue may be used to initialize a const lvalue reference; see
        -- https://en.cppreference.com/w/cpp/language/value_category
        sayable @saytag $ withContext wc (LValRef t)
      RValRef t -> withContext wc t &+ t'"&&"
      ComplexPair t -> withContext wc t &- t'"complex"
      Imaginary t -> withContext wc t &- t'"imaginary"
      ArrayType bnd t -> withContext wc t &+ '[' &+ withContext wc bnd &+ ']'
      Template tp ta -> withContext wc tp &- withContext wc ta -- ??
      Cpp11PackExpansion ts ->
        -- XXX expected some "..." (see
        -- https://en.cppreference.com/w/cpp/language/parameter-pack) but c++filt
        -- does not visibly decorate these.
        ctxLst ts wc
      StdType stdTy -> sayable @saytag $ withContext wc stdTy
      DeclType_ dt -> sayable @saytag $ withContext wc dt


sayFunctionType :: Type_ -> Text -> WithContext Type_ -> Saying saytag
sayFunctionType (Function cvqs mb'exc trns isExternC rTy argTys mb'ref) nm wc =
  ctxLst' cvqs wc " "
  &? wCtx mb'exc wc
  &+ withContext wc trns
  &+ (if isExternC then t'" extern \"C\"" else t'"")
  &+ withContext wc rTy
  &- nm &+ '('
  &+* (case argTys of
          BaseType Void :| [] -> []
          _ -> wCtx (NEL.toList argTys) wc
      )
  &+ ')'
  &? wCtx mb'ref wc
sayFunctionType _ _ _ = cannotSay Demangler "sayFunctionType"
                        [ "Called with a type that is not a Function!" ]


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ArrayBound
  ) => Sayable saytag (WithContext ArrayBound) where
  sayable wc =
    case contextData wc of
      NoBounds -> sayable @saytag $ t'""
      NumBound i -> sayable @saytag i
      ExprBound e -> sayable @saytag $ withContext wc e


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ExceptionSpec
  ) => Sayable saytag (WithContext ExceptionSpec) where
  sayable wc =
    case contextData wc of
      NonThrowing -> sayable @saytag $ t'"noexcept"
      ComputedThrow expr -> t'"throw" &- withContext wc expr -- ?
      Throwing tys -> t'"throw (" &+ wCtx tys wc &+ ')' -- ?

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext Transaction) where
  sayable wc =
    case contextData wc of
      TransactionSafe -> sayable @saytag $ t'"safe" -- ?
      TransactionUnsafe -> sayable @saytag $ t'""

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''BaseType
  ) => Sayable saytag (WithContext BaseType) where
  sayable wc =
    case lookup (contextData wc) builtinTypeTable of
      Just (_,s,_) -> sayable @saytag s
      Nothing ->
        case contextData wc of
          FloatN n -> t'"std::float" &+ n &+ t'"_t"
          FloatNx n -> t'"std::float" &+ n &+ t'"x_t"
          SBitInt n -> t'"signed _BitInt(" &+ n &+ ')'
          UBitInt n -> t'"unsigned _BitInt(" &+ n &+ ')'
          VendorExtendedType nm mb'ta -> withContext wc nm &? wCtx mb'ta wc
          t -> cannotSay Demangler "sayable.Basetype"
               [ "Unknown BaseType not listed in the builtinTypeTable"
               , show t
               ]

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext CallOffset) where
  sayable _wc =
    cannotSay Demangler "Sayable CallOffset"
    [ "The CallOffset is for a thunk or covariant return thunk"
    , "and is not expected to be printed."
    ]

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''SubsCandidate
  ) => Sayable saytag (WithContext SubsCandidate) where
  sayable wc = -- For debug only
    case contextData wc of
      SC_Type t -> t'"SC_Ty" &- withContext wc t
      SC_UQName True n -> t'"SC_UN" &- t'"std::" &+ withContext wc n
      SC_UQName _ n -> t'"SC_UN" &- withContext wc n
      SC_Prefix p -> t'"SC_PR" &- withContext wc p
      SC_TemplatePrefix tp -> t'"SC_TP" &- withContext wc tp
      SC_UnresolvedType urt -> t'"SC_URT" &- withContext wc urt
