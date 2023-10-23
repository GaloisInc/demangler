{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Demangler.Structure
where

import Data.List.NonEmpty ( NonEmpty )
import Data.Text ( Text )
import Numeric.Natural

import Demangler.Context


data Demangled = Original Coord
               | Encoded Encoding
               | VendorExtended Encoding Coord


data Encoding = EncFunc FunctionName (Maybe Type_) (NonEmpty Type_)
              | EncStaticFunc FunctionName (Maybe Type_) (NonEmpty Type_)
              | EncData Name
              | EncSpecial SpecialName
              | EncConstStructData UnqualifiedName
                -- ^ Const data that is not a builtin data type.  Undocumented.
                --
                --  struct foo { int x; };
                --  const struct foo = { 9 };
                --
                -- or:
                --
                --  class foo { int x; };
                --  const class foo = { 9 };
                --
                -- Is encoded as _ZLname where name is the size followed by that
                -- many characters (e.g. _ZL3foo).
  deriving (Eq, Show)

data FunctionName = FunctionName Name
  deriving (Eq, Show)

data Name = NameNested NestedName
          | UnscopedName Bool UnqualifiedName -- Bool is "std::" prefix
          | UnscopedTemplateName Name TemplateArgs
          | LocalName FunctionScope FunctionEntity (Maybe Discriminator)
          | StringLitName FunctionScope (Maybe Discriminator)
  deriving (Eq, Show)

data NestedName = NestedName Prefix UnqualifiedName
                  [CVQualifier] (Maybe RefQualifier)
                | NestedTemplateName TemplatePrefix TemplateArgs
                  [CVQualifier] (Maybe RefQualifier)
  deriving (Eq, Show)

type FunctionScope = Coord
type FunctionEntity = Coord
type Discriminator = Coord

data ModuleName = ModuleName IsPartition UnqualifiedName -- KWQ: just a SourceName
  deriving (Eq, Show)

type IsPartition = Bool

data UnqualifiedName = SourceName Coord
                     | OperatorName Operator [ABI_Tag]
                     | CtorDtorName CtorDtor
                     | StdSubst Substitution
                     | ModuleNamed [ModuleName] UnqualifiedName
                      --  | UnnamedTypeName ...  starts with "U"
                     --  | StructuredBinding ...
  deriving (Eq, Show)

data CtorDtor = CompleteCtor
              | BaseCtor
              | CompleteAllocatingCtor
              | CompleteInheritingCtor Type_
              | BaseInheritingCtor Type_
              | DeletingDtor
              | CompleteDtor
              | BaseDtor
  deriving (Eq, Show)

data Operator = OpNew
              | OpNewArr
              | OpDel
              | OpDelArr
              | OpCoAwait
              | OpPositive
              | OpNegative
              | OpAddress
              | OpDeReference
              | OpComplement
              | OpPlus
              | OpMinus
              | OpMultiply
              | OpDivide
              | OpRemainder
              | OpAnd
              | OpOr
              | OpXOR
              | OpAssign
              | OpAssignPlus
              | OpAssignMinus
              | OpAssignMul
              | OpAssignDiv
              | OpAssignRem
              | OpAssignAnd
              | OpAssignOr
              | OpAssignXOR
              | OpLeftShift
              | OpRightShift
              | OpAssignShL
              | OpAssignShR
              | OpEq
              | OpNotEq
              | OpLT
              | OpGT
              | OpLTE
              | OpGTE
              | OpSpan
              | OpNot
              | OpLogicalAnd
              | OpLogicalOr
              | OpPlusPlus
              | OpMinusMinus
              | OpComma
              | OpPointStar
              | OpPoint
              | OpCall
              | OpIndex
              | OpQuestion
              | OpSizeOfType
              | OpSizeOfExpr
              | OpAlignOfType
              | OpAlignOfExpr
              | OpCast Type_
              | OpString UnqualifiedName
              | OpVendor Natural UnqualifiedName
  deriving (Eq, Show)

data ABI_Tag = ABITag UnqualifiedName
  deriving (Eq, Show)

data SpecialName = VirtualTable Type_
                 | TemplateParameterObj TemplateArg
                 | VTT Type_
                 | TypeInfo Type_ -- struct
                 | TypeInfoName Type_
                 | Thunk CallOffset Encoding
                 | CtorVTable ()
  deriving (Eq, Show)

data CallOffset = VirtualOffset Int Int  -- base override, vcall offset
                | NonVirtualOffset Int   -- base override
  deriving (Eq, Show)

data Substitution' = SubsFirst
                   | Subs Natural  -- Note: converted from Base36 in mangled form
                   | SubsConst Substitution
  deriving Show

data Substitution = SubStd  -- "std::", a prefix, needing subsequent name
                  | SubAlloc -- "std::allocator", a prefix, needs template arg
                  | SubBasicString -- "std::basic_string", needs template args
                  | SubStdType StdType
  deriving (Eq, Show)


data Type_ = BaseType BaseType
           | QualifiedType [ExtendedQualifier] [CVQualifier] Type_
           | ClassUnionStructEnum Name
           | ClassStruct Name
           | Union Name
           | Enum Name
           | Function [CVQualifier] (Maybe ExceptionSpec)
             Transaction Bool Type_ (NonEmpty Type_) (Maybe RefQualifier)
           | Template TemplateParam TemplateArgs
           | Pointer Type_
           | LValRef Type_
           | RValRef Type_
           | ComplexPair Type_
           | Imaginary Type_
           | Cpp11PackExpansion (NonEmpty Type_)
           | StdType StdType
  deriving (Eq, Show)

data ExceptionSpec = NonThrowing
                   | ComputedThrow Expression
                   | Throwing (NonEmpty Type_)
  deriving (Eq, Show)

data Transaction = TransactionSafe | TransactionUnsafe
  deriving (Eq, Show)

data BaseType = Void | Wchar_t | Bool_
              | Char_ | SChar | UChar
              | Short | UShort
              | Int_ | UInt
              | Long | ULong
              | LongLong | ULongLong
              | Int128 | UInt128
              | Float_ | Double_ | LongDouble80 | Float128
              | Ellipsis
              | IEE754rDecFloat64
              | IEE754rDecFloat128
              | IEE754rDecFloat32
              | IEE754rDecFloat16
              | FloatN Natural
              | FloatNx Natural
              | BFloat16
              | SBitInt Natural | UBitInt Natural
              | Char32 | Char16 | Char8
              | Auto | DeclTypeAuto
              | NullPtr
              | N1168FixedPointAccum
              | N1168FixedPointAccumSat
              | N1168FixedPointFract
              | N1168FixedPointFractSat
              | VendorExtendedType UnqualifiedName (Maybe TemplateArgs)
  deriving (Eq, Show)

data StdType = BasicStringChar
             | BasicIStream
             | BasicOStream
             | BasicIOStream
  deriving (Eq, Show)

-- Qualifiers: there may be 0 or more (as expressed via an array) but there will
-- only be one of each, and they are usually expressed in the order shown here,
-- and printed on the right side of the output they qualify in the reverse order
-- shown here.
data CVQualifier = Restrict | Volatile | Const_
  deriving (Eq, Show)
data RefQualifier = Ref | RefRef
  deriving (Eq, Show)
type ExtendedQualifier = () -- XXX TBD

data Prefix = PrefixTemplateParam TemplateParam PrefixR
            | PrefixDeclType DeclType PrefixR
            | PrefixClosure ClosurePrefix -- ??
            | Prefix PrefixR
  deriving (Eq, Show)

data PrefixR = PrefixUQName UnqualifiedName PrefixR
             | PrefixTemplateArgs TemplateArgs PrefixR
             | PrefixEnd
  deriving (Eq, Show)

pattern EmptyPrefix :: Prefix
pattern EmptyPrefix = Prefix PrefixEnd


data TemplatePrefix = GlobalTemplate (NonEmpty UnqualifiedName)
                    | NestedTemplate Prefix (NonEmpty UnqualifiedName)
                    | TemplateTemplateParam TemplateParam
  deriving (Eq, Show)

type TemplateName = Name

type TemplateArgs = NonEmpty TemplateArg

data TemplateArg = TArgType Type_
                 | TArgExpr Expression
                 | TArgSimpleExpr ExprPrimary
                 | TArgPack [TemplateArg]
  deriving (Eq, Show)

type TemplateParam = TemplateArg

data Expression = ExprPack Expression
                | ExprTemplateParam TemplateParam
                | ExprPrim ExprPrimary
  deriving (Eq, Show)

data ExprPrimary = IntLit Type_ Int
                 | FloatLit Type_ Float
                 | DirectLit Type_  -- String or NullPtr
                 | NullPtrTemplateArg Type_
                 | ComplexFloatLit Type_ Float Float
                 | ExternalNameLit Encoding
  deriving (Eq, Show)

type ClosurePrefix = () -- XXX TBD
type DeclType = () -- XXX TBD

-- | Table of builtin types as the internal BaseType representation, followed by
-- a tuple of strings.  The first string is the reference to this type in a
-- mangled name.  The second string is the C/C++ type name to be used when
-- writing a value cast.  The third string, if non-empty, is a C/C++ suffix that
-- can be written after literal values to indicate the type instead (for example,
-- emit `10ul` instead of `(unsigned long)10`).

builtinTypeTable :: [ (BaseType, (Text, Text, Text)) ]
builtinTypeTable =
  [ (Void, ("v", "void", ""))
  , (Wchar_t, ("w", "wchar_t", ""))
  , (Bool_, ("b", "bool", ""))
  , (Char_, ("c", "char", ""))
  , (SChar, ("a", "signed char", ""))
  , (UChar, ("h", "unsigned char", ""))
  , (Short, ("s", "short", ""))
  , (UShort, ("t", "unsigned short", ""))
  , (Int_, ("i", "int", ""))
  , (UInt, ("j", "unsigned int", ""))
  , (Long, ("l", "long", "l"))
  , (ULong, ("m", "unsigned long", "ul"))
  , (LongLong, ("x", "long long", "")) -- __int64
  , (ULongLong, ("y", "unsigned long long", "")) -- __int64
  , (Int128, ("n", "__int128", ""))
  , (UInt128, ("o", "unsigned __int128", ""))
  , (Float_, ("f", "float", ""))
  , (Double_, ("d", "double", ""))
  , (LongDouble80, ("e", "long double", "")) -- __float80
  , (Float128, ("g", "__float128", ""))
  , (Ellipsis, ("z", "...", ""))
  , (IEE754rDecFloat64, ("Dd", "__ieeefloat64", "")) -- ??
  , (IEE754rDecFloat128, ("De", "__ieeefloat128", "")) -- ??
  , (IEE754rDecFloat32, ("Df", "__ieeefloat32", "")) -- ??
  , (IEE754rDecFloat16, ("Dh", "__ieeefloat16", "")) -- ??
  , (BFloat16, ("DF16b", "std::bfloat16_t", ""))
  , (Char32, ("Di", "char32_t", ""))
  , (Char16, ("Ds", "char16_t", ""))
  , (Char8, ("Du", "char8_t", ""))
  , (Auto, ("Da", "auto", ""))
  , (DeclTypeAuto, ("Dc", "decltype(auto)", "")) -- ??
  , (NullPtr, ("Dn", "std::nullptr_t", "")) -- decltype(nullptr)
  , (N1168FixedPointAccum, ("DA", "T _Accum", "")) -- ??
  , (N1168FixedPointAccumSat, ("DS DA", "_Sat T _Accum", "")) -- ??
  , (N1168FixedPointFract, ("DR", "T _Fract", "")) -- ??
  , (N1168FixedPointFractSat, ("DS DR", "_Sat T _Fract", "")) -- ??
  ]

opTable :: [ (Operator, (Text, Text)) ]
opTable =
  [ (OpNew,         ("nw", " new"))
  , (OpNewArr,      ("na", " new[]"))
  , (OpDel,         ("dl", " delete"))
  , (OpDelArr,      ("da", " delete[]"))
  , (OpCoAwait,     ("aw", " co_await"))
  , (OpPositive,    ("ps", "+"))
  , (OpNegative,    ("ng", "-"))
  , (OpAddress,     ("ad", "&"))
  , (OpDeReference, ("de", "*"))
  , (OpComplement,  ("co", "~"))
  , (OpPlus,        ("pl", "+"))
  , (OpMinus,       ("mi", "-"))
  , (OpMultiply,    ("ml", "*"))
  , (OpDivide,      ("dv", "/"))
  , (OpRemainder,   ("rm", "%"))
  , (OpAnd,         ("an", "&"))
  , (OpOr,          ("or", "|"))
  , (OpXOR,         ("eo", "^"))
  , (OpAssign,      ("aS", "="))
  , (OpAssignPlus,  ("pL", "+="))
  , (OpAssignMinus, ("mI", "-="))
  , (OpAssignMul,   ("mL", "*="))
  , (OpAssignDiv,   ("dV", "/="))
  , (OpAssignRem,   ("rM", "%="))
  , (OpAssignAnd,   ("aN", "&="))
  , (OpAssignOr,    ("oR", "|="))
  , (OpAssignXOR,   ("eO", "^="))
  , (OpLeftShift,   ("ls", "<<"))
  , (OpRightShift,  ("rs", ">>"))
  , (OpAssignShL,   ("lS", "<<="))
  , (OpAssignShR,   ("rS", ">>="))
  , (OpEq,          ("eq", "=="))
  , (OpNotEq,       ("ne", "!="))
  , (OpLT,          ("lt", "<"))
  , (OpGT,          ("gt", ">"))
  , (OpLTE,         ("le", "<="))
  , (OpGTE,         ("ge", ">="))
  , (OpSpan,        ("ss", "<=>"))
  , (OpNot,         ("nt", "!"))
  , (OpLogicalAnd,  ("aa", "&&"))
  , (OpLogicalOr,   ("oo", "||"))
  , (OpPlusPlus,    ("pp", "++"))
  , (OpMinusMinus,  ("mm", "--"))
  , (OpComma,       ("cm", ","))
  , (OpPointStar,   ("pm", "->*"))
  , (OpPoint,       ("pt", "->"))
  , (OpCall,        ("cl", "()"))
  , (OpIndex,       ("ix", "[]"))
  , (OpQuestion,    ("qu", "?"))
  , (OpSizeOfType,  ("st", " sizeof"))
  , (OpAlignOfType, ("at", " alignof"))
  , (OpSizeOfExpr,  ("sz", " sizeof"))
  , (OpAlignOfExpr, ("az", " alignof"))
  ]


----------------------------------------------------------------------
-- Core data structure utilized by Substitution but which must be defined for
-- other users.

data SubsCandidate = SC_Type Type_
                   | SC_UQName Bool UnqualifiedName
                     -- ^ Bool is True for std:: namespace prefix
                   | SC_Prefix Prefix
                   | SC_TemplatePrefix TemplatePrefix
  deriving (Eq, Show)
