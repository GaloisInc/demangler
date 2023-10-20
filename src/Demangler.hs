{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Demangler
  (
    Context
  , newDemangling
  , Demangled
  , Result
  , demangle
  , demangle1
  )
where

import           Control.Applicative
import           Control.Lens ( (&), (^.), view, (.~), (||~) )
import           Control.Monad
import           Data.Char
import           Data.Either ( isRight )
import           Data.List.NonEmpty ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty as NEL
import           Data.Maybe
import           Data.Semigroup ( sconcat )
import           Data.Text ( Text )
import qualified Data.Text as T
import           Text.Sayable

import           Demangler.Context
import           Demangler.Engine
import           Demangler.PPrint ()
import           Demangler.Structure
import           Demangler.Substitution

#ifdef MIN_VERSION_panic
-- The debug flag is enabled in the cabal file
import           Debug.Trace
#endif


----------------------------------------------------------------------


-- | Demangle a single entry.  If there are multiple entries to be demangled, use
-- 'demangle' for efficient batching and memory reduction.

demangle1 :: Text -> Result
demangle1 s = demangle s newDemangling

-- | Demangle an input string, given a Context for demangling.
--
-- The signature of this function makes it ideal for State evaluation.

demangle :: Text -> Context -> Result
demangle s c =
  let seed = (s, ((), (c, (mempty, (mempty, False, False))))) in
  case asum (($ seed) <$> [ mangled, plain ]) of
                 Just r -> (r ^. nVal, r ^. nContext)
                 _ -> let (i,c') = contextFindOrAdd s c
                      in (Original i, c')


--------------------
-- Mangled name parsing of various elements

mangled :: Next () Demangled
mangled = match "_Z" >=> encoding >=>
          asum' [ match "." >=> vendorExtension >=> end_of_input
                , end_of_input >=> rmap Encoded
                ]

vendorExtension :: Next Encoding Demangled
vendorExtension x =
  let (i, c') = contextFindOrAdd (x ^. nInp) (x ^. nContext)
  in Just $ x
     & nInp .~ ""
     & nVal .~ VendorExtended (x ^. nVal) i
     & nContext .~ c'

plain :: AnyNext Demangled
plain x =
  let (o, c') = contextFindOrAdd (x ^. nInp) (x ^. nContext)
  in Just $ x
     & nInp .~ ""
     & nVal .~ Original o
     & nContext .~ c'

encoding :: AnyNext Encoding
encoding =
  asum' [ function_name >=> bare_function_type False
        , match "L" >=> function_name >=> bare_function_type True
        , data_name
        , const_struct_data
        , special_name
       ]

function_name :: AnyNext FunctionName
function_name = rmap FunctionName <=< name

data_name :: AnyNext Encoding
data_name = name >=> rmap EncData

const_struct_data :: AnyNext Encoding
const_struct_data = match "L" >=> unqualified_name >=> rmap EncConstStructData

special_name :: AnyNext Encoding
special_name =
  match "T"
  >=> asum' [ match "A" >=> template_arg >=> rmap TemplateParameterObj
            , match "V" >=> type_ >=> rmap VirtualTable
            , match "T" >=> type_ >=> rmap VTT
            , match "I" >=> type_ >=> rmap TypeInfo
            , match "S" >=> type_ >=> rmap TypeInfoName
            , match "c" >=> tbd "covariant return thunk to"
            , match "C" >=> tbd "ctor vtable special name"
            , match "W" >=> tbd "thread-local wrapper routine for"
            , match "H" >=> tbd "thread-local initialization routine for"
            , call_offset >&=> encoding >=> rmap (uncurry Thunk)
            ]
  >=> rmap EncSpecial

call_offset :: AnyNext CallOffset
call_offset = asum' [ match "h" >=> int_number >=> match "_"
                      >=> rmap NonVirtualOffset
                    , match "v" >=> int_number >=> match "_" >&=> digits_num
                      >=> match "_"
                      >=> rmap (uncurry VirtualOffset)
                    ]


int_number :: AnyNext Int
int_number = asum' [ match "n" >=> digits_num >=> rmap ( (-1) * )
                   , digits_num
                   ]

name :: AnyNext Name
name = asum' [ nested_name >=> rmap NameNested
             , unscoped_template_name >&=> template_args
               >=> rmap (uncurry UnscopedTemplateName)
             , local_name
             , unscoped_name
             ]

nested_name :: AnyNext NestedName
nested_name = match "N"
              >=> cv_qualifiers
              >=> optional' ref_qualifier
              -- here: (Maybe [CVQualifier], Maybe RefQualifier)
              >=> asum' [ form1 >=> match "E"
                        , form2 >=> match "E"
                        ]
              >=> dropLastSubst
  where form1 i = do p <- prefix i
                     -- Parse ambiguity here:
                     --
                     --   nested-name ::= N ... <prefix> <unqualified-name> E
                     --   prefix ::= <unqualified-name>
                     --            | <prefix> <unqualified-name>
                     --            | ... others ...
                     --
                     -- Thus, in order to match here, <prefix> *must* have ended
                     -- in an <unqualified-name> match, and that match should be
                     -- removed from the prefix 'p' and used as the final
                     -- <nested-name> element.
                     (rmnpfx, ent) <- prefixInitLast $ p ^. nVal
                     case ent of
                       Right _ -> Nothing
                       Left uq ->
                         case rmnpfx of
                           EmptyPrefix -> Nothing
                           pfx -> let (cvq, mb'refQual) = i ^. nVal
                                  in ret p (NestedName pfx uq cvq mb'refQual)
        form2 i = do pa <- template_prefix_and_args i
                     let (p,mba) = pa ^. nVal
                     a <- mba
                     let (cvq, mb'refQual) = i ^. nVal
                     ret pa $ NestedTemplateName p a cvq mb'refQual

unscoped_name :: AnyNext Name
unscoped_name =
  asum' [ unqualified_name >=> rmap (UnscopedName False)
        , match "St" >=> unqualified_name >=> rmap (UnscopedName True)
        ]

unscoped_template_name :: AnyNext Name
unscoped_template_name i =
  (unscoped_name i >>= canSubstUnscopedTemplateName)
  <|> (substitution i
        >>= substituteUnqualifiedName (rmap StdSubst)
        >>= rmap (UnscopedName False)
      )


local_name :: AnyNext Name
local_name i = do f <- match "Z" i >>= function_encoding
                  c <- match "E" f
                  entity f c <|> stringlit f c
  where
    entity f c = do e <- entity_name c
                    discriminated f e
                      <|> ret e (LocalName (f ^. nVal) (e ^. nVal) Nothing)
    stringlit f c = do s <- match "s" c
                       d <- optional (discriminator s)
                       ret (fromMaybe s d) $ StringLitName (f ^. nVal) (view nVal <$> d)
    discriminated f e = do d <- discriminator e
                           ret d $ LocalName (f ^. nVal) (e ^. nVal) (Just $ d ^. nVal)


-- | Parse any CV qualifiers; always succeeds but might return an empty array.
-- Also note that while it is an array, each entry can appear at most once.
cv_qualifiers :: AnyNext [CVQualifier]
cv_qualifiers =
  let ifPresent v i = rmap (\(a,p) -> if isJust p then v:a else a) i
  in insert []
     >=> optional' (match "K") >=> ifPresent Const_
     >=> optional' (match "V") >=> ifPresent Volatile
     >=> optional' (match "r") >=> ifPresent Restrict

ref_qualifier :: AnyNext RefQualifier
ref_qualifier = asum' [ match "&&" >=> rmap (const RefRef)
                      , match "&" >=> rmap (const Ref)
                      ]

-- | Parse prefix.  This is a bit tricky though.  The BNF specifies:
--
--     prefix ::= <unqualified-name>
--            | <prefix> <unqualified-name>
--            | ... others ...
--            | substitution
--
-- but it cannot be expressed directly that way (it would either stop at the
-- *first* unqualified name, or if the first two were reverse, <prefix> would be
-- infinitely recursive because it would recurse without consuming input.  Note
-- however that a recursive prefix *always* terminates with an
-- <unqualified_name>, and can only recurse on that terminator, so once an
-- <unqualified_name> is parsed, the only remaining possibility is *one* more
-- <unqualified_name> entries.
--
-- In addition, the BNF is incorrect, both from the itanium-abi website, and also
-- in the LLVM code comments, which is slightly different, but still incorrect.
-- The BNF for a prefix indicates recursion can only happen before an unqualified
-- name, which precludes matching something like NS_6vectorIfE3fooE
-- ("matrix::Vector<float>::foo").  The LLVM code itself indicates that the
-- prefix is generally recursive, although a template_param, a decltype, or a
-- substitution may not be preceded by anything else, and template_args cannot be
-- immediately adjacent and must not be the starting element.

prefix :: AnyNext Prefix
prefix i = (prefix'i i)
            <|> (substitution i
                 >>= substitutePrefix substitutionPrefix
                 >>= asum' [ rmap extendPrefix >=> prefix'r2
                           , pure
                           ]
                )
  where
    prefix'i :: AnyNext Prefix
    prefix'i =
      asum' [ template_param
              >=> rmap PrefixTemplateParam
              >=> prefix'r2
              >=> canSubstPrefix
            , decltype
              >=> rmap PrefixDeclType
              >=> prefix'r2
              >=> canSubstPrefix
            , ret' Prefix >=> prefix'r2
              >=> \p2 -> case p2 ^. nVal of
                           EmptyPrefix -> Nothing
                           _ -> pure p2
            ]
    prefix'r2 :: Next (PrefixR -> Prefix) Prefix
    prefix'r2 accum =
      asum [ -- Note that two sets of template_args will not occur
             -- back-to-back... at least for C/C++.  There are two dispositions
             -- that could be taken here:
             --
             -- 1. Ignore it if it happens (we didn't generate the mangled form)
             -- 2. Treat it as a demangling parse error.
             --
             -- The following require statements implements disposition 2;
             -- removing it would switch to disposition 1.
             require (not $ last_is_template_args (accum ^. nVal $ PrefixEnd))
             >> template_args accum
             >>= rmap (\ta sp -> accum ^. nVal $ PrefixTemplateArgs ta sp)
             >>= canSubstAccumPrefix
             >>= prefix'r2
           , unqualified_name accum
             >>= rmap (\uqn sp -> accum ^. nVal $ PrefixUQName uqn sp)
             >>= canSubstAccumPrefix
             >>= prefix'r2
           , substitution accum
             >>= substitutePrefixR substitutionPrefixR
             >>= rmap (\subs -> extendPrefix ((accum ^. nVal) subs))
             >>= prefix'r2
           , rmap ($ PrefixEnd) accum
           ]
    canSubstAccumPrefix :: Next (PrefixR -> Prefix) (PrefixR -> Prefix)
    canSubstAccumPrefix sp = rmap ($ PrefixEnd) sp
                             >>= canSubstPrefix
                             >>= ret' (sp ^. nVal)
    last_is_template_args = maybe False (isRight . snd) . prefixInitLast


substitutionPrefix :: Next Substitution Prefix
substitutionPrefix = rmap (Prefix . ($ PrefixEnd) . PrefixUQName . StdSubst)

substitutionPrefixR :: Next Substitution PrefixR
substitutionPrefixR = rmap (($ PrefixEnd) . PrefixUQName . StdSubst)

decltype :: AnyNext DeclType
decltype = asum' [ match "Dt" >=> expression >=> match "E" >=> tbd "decltype1"
                 , match "DT" >=> expression >=> match "E" >=> tbd "decltype2"
                 ]

closure_prefix :: AnyNext ClosurePrefix
closure_prefix = tbd "closure prefix"

unqualified_name :: AnyNext UnqualifiedName
unqualified_name = asum' [ \i -> do op <- operator_name i
                                    at <- many' abi_tag $ rdiscard op
                                    ret at $ OperatorName (op ^. nVal) (at ^. nVal)
                         , ctor_dtor_name >=> rmap CtorDtorName
                         , source_name
                         , unnamed_type_name
                           -- , match "DC" i >>= some source_name >>= match "E"
                         ]

operator_name :: AnyNext Operator
operator_name =
  let opMatch (o,(t,_)) = match t >=> rmap (const o)
  in asum' ((opMatch <$> opTable)
             <> [ match "cv" >=> type_ >=> rmap OpCast
                , match "li" >=> source_name >=> rmap OpString
                , match "v" >=> single_digit_num >=>
                  \d -> do sn <- source_name d
                           rmap (OpVendor (toEnum $ d ^. nVal)) sn
                ]
           )

abi_tag :: AnyNext ABI_Tag
abi_tag = match "B" >=> source_name >=> rmap ABITag

ctor_dtor_name :: AnyNext CtorDtor
ctor_dtor_name = asum' [ match "C1" >=> ret' CompleteCtor
                       , match "C2" >=> ret' BaseCtor
                       , match "C3" >=> ret' CompleteAllocatingCtor
                       , match "CI1" >=> type_ >=> rmap CompleteInheritingCtor
                       , match "CI2" >=> type_ >=> rmap BaseInheritingCtor
                       , match "D0" >=> ret' DeletingDtor
                       , match "D1" >=> ret' CompleteDtor
                       , match "D2" >=> ret' BaseDtor
                       ]

source_name :: AnyNext UnqualifiedName
source_name = digits_num >=> identifier

identifier :: Next Int UnqualifiedName
identifier i =
  let identChar x = isAlphaNum x || x == '_'
      (nm, ri) = T.splitAt (i ^. nVal) (i ^. nInp)
  in do require (T.all identChar nm)
        let (idnt, c') = contextFindOrAdd nm (i ^. nContext)
        pure $ i
          & nInp .~ ri
          & nVal .~ SourceName idnt
          & nContext .~ c'


unnamed_type_name :: AnyNext UnqualifiedName
unnamed_type_name = tbd "unnamed_type_name"

-- | Parse the function argument (and return) types for a function.
--
-- At this point, all template argments that can be substituted have been made,
-- so any template arguments occurring in the arguments are ignored as T[n]_
-- replacements.

bare_function_type :: Bool -> Next FunctionName Encoding
bare_function_type isStatic i =
  let constr = if isStatic then EncStaticFunc else EncFunc in
  do tys <- types_ $ i & nTmplSubsLock .~ True
     -- Determine if the tys includes a function return type.  The rules are:
     --
     --  1. Template functions have return types encoded, with exceptions below.
     --  2. Function types not appearing as part of a function name mangling
     --     (e.g. parameters, pointer types, etc.) have return type encoded, with
     --     exceptions below.
     --  3. Non-template function names do not have return types encoded
     --
     -- Exceptions (for which return type is never included):
     --
     --  1. Constructors
     --  2. Destructors
     --  3. Conversion operator functions (e.g. operator int(..) )
     --
     let withRetType = let (rty, argtys) = NEL.uncons $ tys ^. nVal
                       in case argtys of
                            Just argtys' ->
                              ret tys (constr (i ^. nVal) (Just rty) argtys')
                            Nothing ->
                              cannot Demangler "bare_function_type.withRetType"
                              [ "Function with rtype and no argtypes: "
                              , sez @"error" (i ^. nVal, i ^. nContext)
                              ]
     let noRetType = rmap (constr (i ^. nVal) Nothing) tys
     case i ^. nVal of
       FunctionName
         (UnscopedTemplateName
           (UnscopedName _ (OperatorName (OpCast {}) _)) _) -> noRetType
       FunctionName (UnscopedTemplateName {}) -> withRetType
       FunctionName (NameNested (NestedTemplateName pr _ _ _)) ->
         case pr of
           NestedTemplate _pfx uqns | CtorDtorName {} <- NEL.last uqns -> noRetType
           _ -> withRetType
       _ ->
#ifdef MIN_VERSION_panic
            -- traceM ("bft what??! " <> show (i ^. nVal)) >>
#endif
            rmap (constr (i ^. nVal) Nothing) tys

-- | Called to return one or more types.  This is essentially the same as `some'
-- type_`, but also handles the case where there might be multiple types returned
-- at once by a Template Argument Pack.

types_ :: AnyNext (NEL.NonEmpty Type_)
types_ = some' type_parser >=> rmap sconcat

-- | Called to parse a *single* type.  If multiple types are obtained (e.g. an
-- Template Argument Pack), return Nothing indicating a parse failure.

type_ :: AnyNext Type_
type_ = type_parser
        >=> \i -> case i ^. nVal of
                    ty :| [] -> ret i ty
                    _ -> cannot Demangler "type_"
                         [ "Can only handle a type_parser return of one type"
                         , "to respond to a location expecting only one."
                         , "bad1: " <> show (i^.nVal)
                         , " rem: " <> T.unpack (i ^. nInp)
                         ]


-- | Returns one or more types.  Normally this should only parse a single type
-- entry, but in the case of Template argument packs, there could actually be
-- multiple types returned.  This should be used as an internal function; callers
-- should use one of the types_ or type_ wrappers to indicate if they can handle
-- multiple types or not.

type_parser :: AnyNext (NEL.NonEmpty Type_)
type_parser =
  asum' [
          -- Matches that are not type substitution candidates
          rmap ((:|[]) . BaseType) <=< builtin_type

          -- Single element matches
        , asum' [ qualified_type
                , function_type
                , class_enum_type
                  -- , array_type
                  -- , pointer_to_member_type
                , template_template_param >&=> template_args
                  >=> rmap (uncurry Template)
                  -- , decltype
                -- This one is tricky: it's recursive, but then binds the
                -- (possibly) multiple returned recursion types into a single
                -- type.
                , match "Dp" >=> type_parser >=> rmap Cpp11PackExpansion
                ]
          >=> canSubstType
          >=> rmap (:|[])

          -- Possibly multiple element matches (either direct or via recursion)
        , asum' [ match "P" >=> type_parser >=> rmap (fmap Pointer)
                , match "R" >=> type_parser >=> rmap (fmap LValRef)
                , match "O" >=> type_parser >=> rmap (fmap RValRef)
                , match "C" >=> type_parser >=> rmap (fmap ComplexPair)
                , match "G" >=> type_parser >=> rmap (fmap Imaginary)
                , template_param
                  >=> (\i ->
                         let retType t = ret i (t :| [])
                         in case i ^. nVal of
                              TArgType t -> retType t
                              TArgPack [] -> retType $ BaseType Ellipsis
                              TArgPack tas ->
                                let each = \case
                                      TArgType t -> t
                                      _ -> fromJust $ cannot Demangler
                                           "type_parser.template_param"
                                           [ "nested TArgPack members:"
                                           , show tas
                                           ]
                                in ret i =<< NEL.nonEmpty (each <$> tas)
                              o -> cannot Demangler "type_parser.template_param"
                                   [ "bad template param ref in type:"
                                   , sez @"debug" (o, i ^. nContext)
                                   , "raw: " <> show o
                                   ]
                      )
                ]
          >=> canSubstTypes

          -- Substitutions, which are not recursively added as a substitution
          -- candidate
        , substitution
          >=> substituteType stdSubstToType
          >=> rmap (:|[])
        ]


builtin_type :: AnyNext BaseType
builtin_type =
  let parse (t,(m,_,_)) = match m >=> ret' t
  in asum'
     ((parse <$> builtinTypeTable)
       <> [ match "DF" >=> digits_num >=> rmap (FloatN  . toEnum) >=> match "_"
          , match "DF" >=> digits_num >=> rmap (FloatNx . toEnum) >=> match "x"
          , match "DB" >=> digits_num >=> rmap (SBitInt . toEnum) >=> match "_" -- TODO: or expression
          , match "DU" >=> digits_num >=> rmap (UBitInt . toEnum) >=> match "_" -- TODO: or expression
          , match "u" >=> source_name >=> optional' template_args
            >=> rmap (uncurry VendorExtendedType)
          ]
     )

qualified_type :: AnyNext Type_
qualified_type i = do eQ <- many' extended_qualifier $ rdiscard i
                      cQ <- cv_qualifiers eQ
                      -- Require some amount of production before recursion
                      require $ not $ and [ null $ cQ ^. nVal
                                          , null $ eQ ^. nVal
                                          ]
                      tY <- type_ cQ
                      ret tY $ QualifiedType (eQ ^. nVal) (cQ ^. nVal) (tY ^. nVal)

extended_qualifier :: Next () ExtendedQualifier
extended_qualifier = tbd "extended_qualifier"

function_type :: AnyNext Type_
-- function_type = tbd "function_type"
function_type i = do f0 <- cv_qualifiers i
                           >>= optional' exception_spec
                           >>= optional' (match "Dx")
                     let ((cvq, mb'exc), mb'dx) = f0 ^. nVal
                     f1 <- match "F" f0 >>= optional' (match "Y")
                     let isExternC = isJust $ snd $ f1 ^. nVal
                     tys <- types_ f1
                     let (rty, tyrem) = NEL.uncons $ tys ^. nVal
                     argtys <- tyrem
                     f2 <- optional' ref_qualifier tys
                           >>= match "E"
                     let trnsct = if isJust mb'dx
                                  then TransactionSafe
                                  else TransactionUnsafe
                     ret f2 (Function cvq mb'exc trnsct isExternC
                             rty argtys (snd $ f2 ^. nVal))

exception_spec :: AnyNext ExceptionSpec
exception_spec = asum' [ match "Do" >=> ret' NonThrowing
                       , match "DO" >=> expression >=> match "E"
                         >=> rmap ComputedThrow
                       , match "Dw" >=> types_ >=> match "E"
                         >=> rmap Throwing
                       ]

class_enum_type :: AnyNext Type_
class_enum_type = asum' [ rmap ClassUnionStructEnum <=< name
                        , match "Ts" >=> rmap ClassStruct <=< name
                        , match "Tu" >=> rmap Union <=< name
                        , match "Te" >=> rmap Enum <=< name
                        ]

function_encoding :: AnyNext FunctionScope
function_encoding = tbd "function_encoding"

entity_name :: Next a FunctionEntity
entity_name = tbd "entity_name"

discriminator :: Next a Int
discriminator = asum' [ match "_" >=> single_digit_num
                      , match "__" >=> digits_num >=> match "_"
                      ]

template_prefix_and_args :: AnyNext (TemplatePrefix, Maybe TemplateArgs)
template_prefix_and_args =
  asum' [ asum' [ \i -> do p <- prefix i
                           (tpr, entas) <- prefixInitLast (p ^. nVal)
                           (rmnpval, ent) <- prefixInitLast tpr
                           case ent of
                             Right _ ->
                               cannot Demangler "template_prefix_and_args"
                               ["Penultimate prefix must be an UnqualifiedName"]
                             Left un ->
                               case entas of
                                 Left _ ->
                                   cannot Demangler "template_prefix_and_args"
                                   [ "Ultimate prefix must be template args" ]
                                 Right tas ->
                                   let constr = case rmnpval of
                                                  EmptyPrefix -> GlobalTemplate
                                                  p' -> NestedTemplate p'
                                   in ret p (constr (un :| []), Just tas)
                   , template_param >=> rmap ((, Nothing) . TemplateTemplateParam)
                   ]
           , substitution >=> substituteTemplatePrefix
             (\s -> cannot Demangler "template_prefix_and_args"
                    [ "Not a template prefix substitute:"
                    , show (s ^. nVal)
                    ]
             )
             >=> rmap (, Nothing)
           ]


template_template_param :: AnyNext TemplateParam
template_template_param i = (template_param i >>= canSubstTemplateParam)
                            <|> (substitution i >>= tbd "ttp subs")

-- | Process a set of template args.
--
-- Note that only the *outermost* and *final* set of template args should be
-- candidates for substitution.
--
--   foo<bar<int> >              --->   [ bar<int> ]
--   foo<int>::bar<float, char>  --->  [ float, char ]
--
-- The nTmplSubsLatch and lTmplSubsLock form a two-phase state management: both
-- start as false and lock is one cycle after latch.  When locked, no new
-- template substitutions can be made.  Thus, recursion is handled by the first
-- (outermost) set of template parameters setting latch, which means that any
-- subsequent of (recursive) template parameters will set lock and therefore will
-- not update any template parameter substitution candidates.
--
-- The *final* set is handled by clearing the set of template parameter
-- substitution candidates any time this is entered and latch isn't set (latch is
-- cleared when each outer-level template parameter parsing is completed or has
-- not yet started).
--
-- One additional constraint is that template parameters are only substitution
-- candidates if encountered in the function "name" portion, but once function
-- arguments are processed, no more template argument candidates are added.  This
-- is accomplished by the argument processing setting the lock, and not doing any
-- clearing here when lock is set.

template_args :: AnyNext TemplateArgs
template_args = match "I"
                >=> (\i -> do let latched = i ^. nTmplSubsLatch
                                  locked = i ^. nTmplSubsLock
                                  lock = latched
                                  enter = (nTmplSubsLatch .~ True)
                                          . (nTmplSubsLock ||~ lock)
                                  i' = if latched || locked
                                          -- reads: if outermost and not reading
                                          -- function arguments
                                       then i & enter
                                       else i & enter & nTmplSubs .~ mempty
                              r <- some' template_arg i'
                              pure
                                $ r
                                & nTmplSubsLatch .~ latched
                                & nTmplSubsLock .~ locked
                    )
                >=> match "E"

template_arg :: AnyNext TemplateArg
template_arg =
  asum' [ type_ >=> rmap TArgType >=> canSubstTemplateArg
        , match "X" >=> expression >=> match "E" >=> rmap TArgExpr
        , expression_primary >=> rmap TArgSimpleExpr >=> canSubstTemplateArg
        , match "J"
          >=> (\i -> do let locked = i ^. nTmplSubsLock
                        r <- many' template_arg . rdiscard $ i & nTmplSubsLock .~ True
                        l <- match "E" r
                        rmap TArgPack $ l & nTmplSubsLock .~ locked
              )
          >=> canSubstTemplateArg
        ]

template_param :: AnyNext TemplateParam
template_param =
  asum' [ match "T_" >=> ret' Nothing
        , match "T" >=> digits_num >=> rmap Just >=> match "_"
        ]
  >=> substituteTemplateParam

expression :: AnyNext Expression
expression = asum' [ match "sp" >=> expression >=> rmap ExprPack
                   , template_param >=> rmap ExprTemplateParam
                   , expression_primary >=> rmap ExprPrim
                   , tbd "expression"
                   ]

expression_primary :: AnyNext ExprPrimary
expression_primary =
  let toFloat w f = read (show w <> "." <> show f)
      floatLit ty w p = FloatLit (ty ^. nVal) $ toFloat (w ^.nVal) p
      complexLit ty w p iw ip =
        ComplexFloatLit (ty ^. nVal) (toFloat (w ^. nVal) (p ^. nVal)) (toFloat (iw ^. nVal) ip)
      withType t = asum [ do d <- digits_num t
                             asum [ do r <- match "." d >>= digits_num
                                       asum [ do i <- match "_" r
                                                      >>= digits_num
                                                      >>= match "."
                                                 ir <- digits_num i
                                                 rmap (complexLit t d r i) ir
                                            , rmap (floatLit t d) r
                                            ]
                                  , rmap (IntLit (t ^. nVal)) d
                                  ]
                        , rmap DirectLit t
                        ]
  in
    match "L"
    >=> asum' [ type_ >=> withType >=> match "E"
              , match "_Z" >=> encoding >=> match "E" >=> rmap ExternalNameLit
              ]