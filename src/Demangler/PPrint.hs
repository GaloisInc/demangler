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

ctxLst :: forall saytag t a .
          Sayable saytag (WithContext a)
       => Functor t
       => Foldable t
       => t a -> Context -> Saying saytag
ctxLst l c = t'"" &+* wCtx l c

ctxLst' :: Sayable saytag (WithContext a)
        => Functor t
        => Foldable t
        => t a -> Context -> Text -> Saying saytag
ctxLst' l c sep = sep &:* wCtx l c

wCtx :: Functor t => t a -> Context -> t (WithContext a)
wCtx a c = (\b -> WC b c) <$> a


----------------------------------------------------------------------
-- Sayable instances for printing demangled results

instance {-# OVERLAPPING #-}
  ( Sayable "diagnostic" (WithContext Encoding)
  ) => Sayable "diagnostic" Result where
  sayable = \case
    (Original i, c) -> contextStr c i &- t'"{orig}"
    (Encoded e, c) -> sayable @"diagnostic" $ WC e c
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr c i
      in WC d c &- t'"[clone" &- s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  ( Sayable saytag (WithContext Encoding)
  ) => Sayable saytag Result where
  sayable = \case
    (Original i, c) -> sayable @saytag $ contextStr c i
    (Encoded e, c) -> sayable @saytag $ WC e c
    (VendorExtended d i, c) ->
      let (s1,s2) = T.span isAlphaNum $ contextStr c i
      in WC d c &- t'"[clone" &- '.' &+ s1 &+ ']' &+ s2

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Encoding
  ) => Sayable saytag (WithContext Encoding) where
  sayable (WC n c) =
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
      EncConstStructData nm -> sayable @saytag $ WC nm c
      EncData nm -> sayable @saytag $ WC nm c
      EncSpecial sn -> sayable @saytag $ WC sn c

sayFunction :: Sayable saytag (WithContext Type_)
            => Context -> FunctionName -> Maybe Type_ -> [Type_] -> Saying saytag
sayFunction c fn mbRet args =
  let (nm,q) = cleanFunctionName fn
      part1 = case mbRet of
                Nothing -> WC nm c &+ t'""
                Just rty -> WC rty c &- WC nm c
      part2 = part1 &+ '(' &+ ctxLst args c &+ ')'
  in if null q then part2 else part2 &- ctxLst' q c " "

instance Sayable saytag (WithContext a)
  => Sayable saytag (NonEmpty (WithContext a)) where
  sayable l = t'"" &+* l

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext a)
  => Sayable saytag (WithContext (NonEmpty a)) where
  sayable (WC l c) = ctxLst l c

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
  sayable (WC n c) =
    case n of
      VirtualTable ty -> t'"vtable for" &- WC ty c
      TemplateParameterObj ta -> t'"template parameter object for" &- WC ta c
      VTT ty -> t'"VTT for" &- WC ty c
      TypeInfo ty -> t'"typeinfo for" &- WC ty c
      TypeInfoName ty -> t'"typeinfo name for" &- WC ty c
      CtorVTable _ -> t'"construction vtable for" &- t'"()"
      Thunk (VirtualOffset _o1 _o2) enc -> t'"virtual thunk to" &- WC enc c
      Thunk (NonVirtualOffset _o1) enc -> t'"non-virtual thunk to" &- WC enc c


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''FunctionName
  ) => Sayable saytag (WithContext FunctionName) where
  sayable (WC n c) = sayable @saytag $ WC n c


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Name
  ) => Sayable saytag (WithContext Name) where
  sayable (WC n c) =
    case n of
      NameNested nn -> sayable @saytag $ WC nn c
      UnscopedName False uqn -> sayable @saytag $ WC uqn c
      UnscopedName True uqn -> t'"std::" &+ WC uqn c
      UnscopedTemplateName nn ta -> WC nn c &+ WC ta c
      LocalName fs fe mbd -> WC fs c  &+ t'"::" &+ WC fe c &? wCtx mbd c -- ??
      StringLitName fs mbd -> WC fs c &? wCtx mbd c -- ??


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext Coord) where
  sayable (WC i c) = sayable @saytag $ contextStr c i


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''UnqualifiedName
  ) =>  Sayable saytag (WithContext UnqualifiedName) where
  sayable (WC n c) =
    case n of
      SourceName i [] -> sayable @saytag $ WC i c
      SourceName i tags -> WC i c &+ ctxLst' tags c ""
      OperatorName op [] -> sayable @saytag $ WC op c
      OperatorName op tags -> WC op c &+ ctxLst' tags c ""
      CtorDtorName cd -> sayable @saytag $ WC cd c
      StdSubst subs -> sayable @saytag $ WC subs c
      ModuleNamed mn uqn -> ctxLst' mn c "" &+ WC uqn c

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''SourceName
   ) => Sayable saytag (WithContext SourceName) where
  sayable (WC (SrcName i) c) = sayable @saytag $ contextStr c i


instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''PrefixUQN)
  , Sayable saytag (WithContext PrefixCDtor)
  ) =>  Sayable saytag (WithContext PrefixUQN) where
  sayable (WC (PUC p n) c) =
    case n of
      CtorDtorName cd -> sayable @saytag $ WC (PCDC p cd) c
      _ -> sayable @saytag $ WC n c

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ModuleName
  ) => Sayable saytag (WithContext ModuleName) where
  sayable (WC (ModuleName isP sn) c) =
    if isP
    then WC sn c &+ ':'
    else WC sn c &+ '.'

{- | Use Sayable (Prefix, CtorDtor, Context) instead, since CtorDtor needs to
   reproduce Prefix name. -}
instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''CtorDtor
   ) =>  Sayable saytag (WithContext CtorDtor) where
  sayable (WC n c) =
    case n of
      CompleteCtor -> 'c' &+ '1'
      BaseCtor -> 'c' &+ '2'
      CompleteAllocatingCtor -> 'c' &+ '3'
      CompleteInheritingCtor t -> t'"ci1" &+ WC t c
      BaseInheritingCtor t -> t'"ci2" &+ WC t c
      DeletingDtor -> 'd' &+ '0'
      CompleteDtor -> 'd' &+ '1'
      BaseDtor -> 'd' &+ '2'

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''PrefixCDtor
  ) =>  Sayable saytag (WithContext PrefixCDtor) where
  sayable (WC (PCDC p n) c) =
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
             CompleteCtor -> sayable @saytag $ WC ln c
             BaseCtor -> sayable @saytag $ WC ln c
             CompleteAllocatingCtor -> sayable @saytag $ WC ln c
             CompleteInheritingCtor t -> sayable @saytag $ WC t c -- ??
             BaseInheritingCtor t -> sayable @saytag $ WC t c -- ??
             DeletingDtor -> '~' &+ WC ln c
             CompleteDtor -> '~' &+ WC ln c
             BaseDtor -> '~' &+ WC ln c
         Nothing -> t'"unk_" &+ WC n c -- unlikely... and will be wrong


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Operator
  ) =>  Sayable saytag (WithContext Operator) where
  sayable (WC op c) =
    case lookup op opTable of
      Just (_, o) -> t'"operator" &+ o
      Nothing ->
        case op of
          OpCast ty -> t'"operator" &- WC ty c
          OpString snm -> sayable @saytag $ WC snm c
          OpVendor n snm -> t'"vendor" &- n &- WC snm c
          _ -> cannotSay Demangler "sayable"
               [ "Operator not in opTable or with a specific override:"
               , show op
               ]

instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''NestedName)
  , Sayable saytag (WithContext PrefixCDtor)
  ) => Sayable saytag (WithContext NestedName) where
  sayable (WC n c) =
    let qualrefs q r = ctxLst' q c " " &? wCtx r c
    in case n of
      NestedName p (CtorDtorName nm) q r ->
        qualrefs q r &+ WC p c &+ t'"::" &+ WC (PCDC p nm) c
      NestedName EmptyPrefix nm q r -> qualrefs q r &+ WC nm c
      NestedName p nm q r -> qualrefs q r &+ WC p c &+ t'"::" &+ WC nm c
      NestedTemplateName tp ta q r -> qualrefs q r &+ WC tp c &+ WC ta c


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Prefix
  ) => Sayable saytag (WithContext Prefix) where
  sayable (WC p c) =
    case p of
      PrefixTemplateParam tp prefixr -> WC tp c &+ WC prefixr c
      PrefixDeclType dt prefixr -> WC dt c &+ WC prefixr c
      PrefixClosure cp -> sayable @saytag $ WC cp c -- ??
      Prefix prefixr -> sayable @saytag $ WC prefixr c

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''PrefixR
  ) => Sayable saytag (WithContext PrefixR) where
  sayable (WC p c) =
    case p of
      PrefixUQName uqn pfr@(PrefixUQName {}) -> WC uqn c &+ t'"::" &+ WC pfr c
      PrefixUQName uqn pfr -> WC uqn c &+ WC pfr c
      PrefixTemplateArgs ta pfr -> WC ta c &+ WC pfr c
      PrefixEnd -> sayable @saytag $ t'""


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext CVQualifier) where
  sayable (WC q _c) =
    case q of
      Restrict -> sayable @saytag $ t'"restrict"
      Volatile -> sayable @saytag $ t'"volatile"
      Const_ -> sayable @saytag $ t'"const"

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext RefQualifier) where
  sayable (WC q _c) =
    case q of
      Ref -> sayable @saytag '&'
      RefRef -> sayable @saytag $ t'"&&"

instance {-# OVERLAPPABLE #-}
  ($(sayableConstraints ''TemplatePrefix)
  , Sayable saytag (WithContext PrefixUQN)
  ) => Sayable saytag (WithContext TemplatePrefix) where
  sayable (WC p c) =
    case p of
      GlobalTemplate uqns -> ctxLst' uqns c "::"
      NestedTemplate pr uqns -> WC pr c &+ t'"::"
                                &+ ctxLst' (PUC pr <$> uqns) c "::"
      TemplateTemplateParam tp -> sayable @saytag $ WC tp c


instance {-# OVERLAPPABLE #-}
  (Sayable saytag (WithContext TemplateArg)
  ) => Sayable saytag (WithContext TemplateArgs) where
  sayable (WC args c) = '<' &+ ctxLst args c &+ templateArgsEnd args

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
  $(sayableConstraints ''TemplateArg
  ) => Sayable saytag (WithContext TemplateArg) where
  sayable (WC p c) =
    case p of
      TArgType ty -> sayable @saytag $ WC ty c
      TArgSimpleExpr ep -> sayable @saytag $ WC ep c
      TArgExpr expr -> sayable @saytag $ WC expr c
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
  $(sayableConstraints ''Expression
  ) => Sayable saytag (WithContext Expression) where
  sayable (WC e c) =
    case e of
      ExprPack expr -> sayable @saytag $ WC expr c
      ExprTemplateParam tp -> sayable @saytag $ WC tp c
      ExprPrim pe -> sayable @saytag $ WC pe c


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ExprPrimary
  ) => Sayable saytag (WithContext ExprPrimary) where
  sayable (WC e c) =
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
                            _ -> '(' &+ WC ty c &+ ')' &+ n
          _ -> '(' &+ WC ty c &+ ')' &+ n
      FloatLit ty n -> '(' &+ WC ty c &+ ')' &+ n
      ComplexFloatLit ty r i -> '(' &+ WC ty c &+ ')' &+ '(' &+ r &+ ',' &- i &+ ')'
      DirectLit ty -> '(' &+ WC ty c &+ t'")NULL"  -- except String?
      NullPtrTemplateArg ty -> '(' &+ WC ty c &+ t'")0"
      ExternalNameLit enc -> sayable @saytag $ WC enc c


instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext ClosurePrefix) where
  sayable (WC _p _c) = cannotSay Demangler "sayable"
                       [ "No Sayable for ClosurePrefix" ]

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Substitution
  ) => Sayable saytag (WithContext Substitution) where
  sayable (WC p c) =
    case p of
      SubStd -> t'"std" &+ t'""
      SubAlloc -> t'"std" &+ t'"::allocator"
      SubBasicString -> t'"std" &+ t'"::basic_string"
      SubStdType stdTy -> sayable @saytag $ WC stdTy c

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext StdType) where
  sayable (WC stdTy _c) =
    let ct = t'"std::char_traits<char>" in
    case stdTy of
      BasicStringChar -> t'"std::basic_string<char," &- ct &+ t'", std::allocator<char> >"
      BasicIStream -> t'"std::basic_istream<char," &- ct &- '>'
      BasicOStream -> t'"std::basic_ostream<char," &- ct &- '>'
      BasicIOStream -> t'"std::basic_iostream<char," &- ct &- '>'


-- n.b. LLVM and GNU syntax seems to be [abi:foo][abi:bar], despite the website
-- documentation of [[gnu::abi_tag ("foo", "bar")]]
instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ABI_Tag
  ) => Sayable saytag (WithContext ABI_Tag) where
  sayable (WC (ABITag p) c) = t'"[abi:" &+ WC p c &+ ']'

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''Type_
 ) => Sayable saytag (WithContext Type_) where
  sayable (WC ty c) =
    case ty of
      BaseType t -> sayable @saytag $ WC t c
      QualifiedType [] [] t -> sayable @saytag $ WC t c
      QualifiedType eqs [] t -> WC t c &+ ctxLst' eqs c " "
      QualifiedType [] cvqs t -> WC t c &- ctxLst' cvqs c " "
      QualifiedType eqs cvqs t -> WC t c &- ctxLst' eqs c " " &- ctxLst' cvqs c " "
      ClassUnionStructEnum n -> sayable @saytag $ WC n c
      ClassStruct n -> sayable @saytag $ WC n c
      Union n -> sayable @saytag $ WC n c
      Enum n -> sayable @saytag $ WC n c
      Function {} -> sayFunctionType ty "" c
      Pointer f@(Function {}) -> sayFunctionType f "(*)" c
      Pointer (ArrayType bnd t) -> WC t c &- t'"(*)" &- '[' &+ WC bnd c &+ ']'
      Pointer t -> WC t c &+ '*'
      LValRef (ArrayType bnd t) -> WC t c &- t'"(&)" &- '[' &+ WC bnd c &+ ']'
      LValRef t -> WC t c &+ '&'
      RValRef t -> WC t c &+ t'"&&"
      ComplexPair t -> WC t c &- t'"complex"
      Imaginary t -> WC t c &- t'"imaginary"
      ArrayType bnd t -> WC t c &+ '[' &+ WC bnd c &+ ']'
      Template tp ta -> WC tp c &- WC ta c -- ??
      Cpp11PackExpansion ts ->
        -- XXX expected some "..." (see
        -- https://en.cppreference.com/w/cpp/language/parameter-pack) but c++filt
        -- does not visibly decorate these.
        ctxLst ts c
      StdType stdTy -> sayable @saytag $ WC stdTy c


sayFunctionType :: Type_ -> Text -> Context -> Saying saytag
sayFunctionType (Function cvqs mb'exc trns isExternC rTy argTys mb'ref) nm c =
  ctxLst' cvqs c " "
  &? wCtx mb'exc c
  &+ WC trns c
  &+ (if isExternC then t'" extern \"C\"" else t'"")
  &+ WC rTy c
  &- nm &+ '('
  &+* (case argTys of
          BaseType Void :| [] -> []
          _ -> wCtx (NEL.toList argTys) c
      )
  &+ ')'
  &? wCtx mb'ref c
sayFunctionType _ _ _ = cannotSay Demangler "sayFunctionType"
                        [ "Called with a type that is not a Function!" ]


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ArrayBound
  ) => Sayable saytag (WithContext ArrayBound) where
  sayable (WC n c) =
    case n of
      NoBounds -> sayable @saytag $ t'""
      NumBound i -> sayable @saytag i
      ExprBound e -> sayable @saytag $ WC e c


instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''ExceptionSpec
  ) => Sayable saytag (WithContext ExceptionSpec) where
  sayable (WC exc c) =
    case exc of
      NonThrowing -> sayable @saytag $ t'"noexcept"
      ComputedThrow expr -> t'"throw" &- WC expr c -- ?
      Throwing tys -> t'"throw (" &+ wCtx tys c &+ ')' -- ?

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext Transaction) where
  sayable (WC trns _c) =
    case trns of
      TransactionSafe -> sayable @saytag $ t'"safe" -- ?
      TransactionUnsafe -> sayable @saytag $ t'""

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''BaseType
  ) => Sayable saytag (WithContext BaseType) where
  sayable (WC t c) =
    case lookup t builtinTypeTable of
      Just (_,s,_) -> sayable @saytag s
      Nothing ->
        case t of
          FloatN n -> t'"std::float" &+ n &+ t'"_t"
          FloatNx n -> t'"std::float" &+ n &+ t'"x_t"
          SBitInt n -> t'"signed _BitInt(" &+ n &+ ')'
          UBitInt n -> t'"unsigned _BitInt(" &+ n &+ ')'
          VendorExtendedType nm mb'ta -> WC nm c &? wCtx mb'ta c
          _ -> cannotSay Demangler "sayable.Basetype"
               [ "Unknown BaseType not listed in the builtinTypeTable"
               , show t
               ]

instance {-# OVERLAPPABLE #-} Sayable saytag (WithContext CallOffset) where
  sayable (WC _co _c) =
    cannotSay Demangler "Sayable CallOffset"
    [ "The CallOffset is for a thunk or covariant return thunk"
    , "and is not expected to be printed."
    ]

instance {-# OVERLAPPABLE #-}
  $(sayableConstraints ''SubsCandidate
  ) => Sayable saytag (WithContext SubsCandidate) where
  sayable (WC cand c) = -- For debug only
    case cand of
      SC_Type t -> t'"SC_Ty" &- WC t c
      SC_UQName True n -> t'"SC_UN" &- t'"std::" &+ WC n c
      SC_UQName _ n -> t'"SC_UN" &- WC n c
      SC_Prefix p -> t'"SC_PR" &- WC p c
      SC_TemplatePrefix tp -> t'"SC_TP" &- WC tp c
