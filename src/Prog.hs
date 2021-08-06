module Prog where

import Data.String (IsString(..))

import Pretty

data Prog
  = Var Name
  | Lam Abstr
  | Pi  Abstr
  | App Prog Prog

  | Star

  | LetRec [Signature] [Prog] Prog
  | Let Decl Prog

  | Rec [FieldDecl]
  | New [Decl]
  | Get Prog Name

  | Ctr Name Type
  | Mtc Prog [Alt]

  | Con Constant Type
  | Hole
  deriving stock (Eq, Ord)
  deriving Show via PP Prog

type Type = Prog
type Kind = Prog

data Abstr = Abstr Signature Prog
  deriving stock (Eq, Ord)

data Decl
  = Bind Signature Prog
  deriving stock (Eq, Ord)
  deriving Show via PP Decl

data Alt
  = Alt Pat Prog
  deriving stock (Eq, Ord)
  deriving Show via PP Alt

data Pat
  = IsVar Name
  | IsCtr Name [Pat]
  | IsCon Constant
  | As    Pat Pat
  | Wild
  deriving stock (Eq, Ord)
  deriving Show via PP Pat

data Name
  = Name String Int
  deriving stock (Eq, Ord)
  deriving Show via PP Name

data Constant
  = Constant String
  deriving stock (Eq, Ord)
  deriving Show via PP Constant

data FieldDecl = FieldDecl Name Type
  deriving stock (Eq, Ord)
  deriving Show via PP FieldDecl

data Signature = Signature { sigName :: Name, sigType :: Type }
  deriving stock (Eq, Ord)
  -- deriving Show via PP Signature

instance Pretty Name where
  pretty (Name n (-1)) = text n
  pretty (Name n ix)   = text n <.> color black ("'" <.> pretty ix)

instance IsString Name     where fromString = flip Name (-1)
instance IsString Prog     where fromString = Var   . fromString
instance IsString Pat      where fromString = IsVar . fromString
instance IsString Constant where fromString = Constant

instance Pretty FieldDecl where
  pretty (FieldDecl n t) = decl n <+> ":" `indent` pretty t

instance Pretty Prog where
  prettyAtPrec p = \case
    Var name -> pretty name
    Lam a ->
      parensIf (p < 7)
        $ collectLam a \(n : ns) b ->
            punct "\\" <+> pretty n
            `above` block (map (("," <+>) . pretty) ns) <+> punct "->"
            `indent` prettyAtPrec 7 b

    Pi a ->
      parensIf (p < 7)
        $ collectPi  a \n b ->
            parensIf True (pretty n) <+> punct "=>"
            `indent` prettyAtPrec 7 b

    App f x  ->
      parensIf (p < 5)
        $ prettyAtPrec 5 f <+> prettyAtPrec 4 x

    Star -> color magenta "Type"

    LetRec ns ds b ->
      parensIf (p < 7)
        $ kw "let" <+> notice "rec"
        `indent` block (zipWith Bind ns ds)
        `above`  kw "in"
        `indent` prettyAtPrec 7 b

    Let d b ->
      parensIf (p < 7)
        $ kw "let" <+> pretty d <+> kw "in"
        `above` prettyAtPrec 7 b

    Ctr n t  -> parensIf (p < 9) $ color (faint magenta) (pretty n) <+> ":" <+> pretty t
    Rec ds   -> "Rec" <+> "{" `indent` block ds `above` "}"
    New ds   -> "{" `indent` block ds `above` "}"
    Get p n  -> prettyAtPrec 0 p <.> punct "." <.> pretty n
    Mtc p as -> kw "case" <+> pretty p <+> kw "of" $$ vcat (map (("|" <+>) . pretty) as)
    Con c t  -> parensIf (p < 10) $ con c <+> ":" <+> pretty t
    Hole     -> color magenta "_"

instance Pretty Decl where
  pretty = \case
    Bind s p -> color (faint yellow) "value" <+> pretty s <+> kw "=" `indent` pretty p

instance Pretty Signature where
  pretty (Signature n t) = prop n <+> punct ":" <+> pretty t

instance Pretty Alt where
  pretty = \case
    Alt p b -> pretty p <+> punct "->" `indent` pretty b

instance Pretty Pat where
  prettyAtPrec p = \case
    IsVar n -> decl n
    IsCtr n [] -> ctor n
    IsCtr n ps -> parensIf (p <= 5) $ ctor n <+> fsep (map (prettyAtPrec 5) ps)
    IsCon c -> pretty c
    As a b -> parensIf (p < 6) $ prettyAtPrec 6 a <+> kw "as" <+> prettyAtPrec 6 b
    Wild -> kw "_"

instance Pretty Constant where
  pretty (Constant c) = text c

kw = color (faint green)
punct = color (faint cyan)

notice, kw, punct :: Doc -> Doc
notice = color red

prop, decl, ctor, con :: Pretty n => n -> Doc
prop = colored (bright yellow)
decl = colored yellow
ctor = colored magenta
con  = colored blue

parensIf = makeParensIf (punct "(", punct ")")

data Annot = Annot Name Type

instance Pretty Annot where
  pretty (Annot n t) = pretty n <+> ":" <+> pretty t

collectLam :: Abstr -> ([Annot] -> Prog -> r) -> r
collectLam (Abstr (Signature n t) b) ret =
  case b of
    Lam a ->
      collectLam a \ns b ->
        ret (Annot n t : ns) b
    _ ->
      ret [Annot n t] b

collectPi :: Abstr -> (Annot -> Prog -> r) -> r
collectPi (Abstr (Signature n t) b) ret =
  ret (Annot n t) b

infix 0 =:
n =: b = Bind (Signature n Hole) b

letrec ds b = LetRec ns bs b
  where
    (ns, bs) = unzip ds

let_ ds b = foldr Let b ds

infixr 1 -->, ==>

(n, t) --> b = Lam (Abstr (Signature n t) b)
(n, t) ==> b = Pi  (Abstr (Signature n t) b)

infixl 2 <|

(<|) = App
