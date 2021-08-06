
{- | An extension of 'Text.PrettyPrint'.
-}

module Pretty
  ( module Pretty
  , module Text.PrettyPrint
  , module Color
  )
  where

import qualified Data.Text as Text
import Data.Text (Text, pack)

import Text.PrettyPrint hiding ((<>))

import Color

-- | Pretty-print to `Text`. Through `String`. Yep.
ppToText :: Pretty a => a -> Text
ppToText = pack . show . pretty

{- | A typeclass for pretty-printable stuff.
-}
class Pretty p where
  pretty :: p -> Doc
  pretty = prettyAtPrec 10

  prettyAtPrec :: Int -> p -> Doc
  prettyAtPrec _ = pretty

  {-# minimal pretty | prettyAtPrec #-}

makeParensIf :: (Doc, Doc) -> Bool -> Doc -> Doc
makeParensIf (open, close) yes d
  | yes       = open <.> d <.> close
  | otherwise = d

instance Pretty () where
  pretty _ = "()"

instance Pretty1 Maybe where
  pretty1 = maybe empty pretty

instance {-# OVERLAPS #-} (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty Int where
  pretty = int

instance Pretty Integer where
  pretty = integer

instance Pretty Float where
  pretty = float

-- | Common instance.
instance Pretty Text where
  pretty = text . Text.unpack

-- | Common instance.
instance Pretty Doc where
  pretty = id
{- | A typeclass for pretty-printable functors.
-}
class Pretty1 p where
  pretty1 :: p Doc -> Doc
  pretty1 = prettyAtPrec1 10

  prettyAtPrec1 :: Int -> p Doc -> Doc
  prettyAtPrec1 _ = pretty1

  {-# minimal pretty1 | prettyAtPrec1 #-}

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty1 p, Functor p) => Pretty (p a) where
  pretty = pretty1 . fmap pretty
  prettyAtPrec prec = prettyAtPrec1 prec . fmap pretty

instance Pretty1 [] where
  pretty1 = list

{- | A wrapper to make `Show` instances from `Pretty` ones.

     > data X a = X
     >   deriving Show via PP (X a)
-}
newtype PP a = PP { unPP :: a }

instance Pretty a => Show (PP a) where
  show = show . pretty . unPP

{- | The class for annotations.
-}
class Modifies d where
  ascribe :: d -> Doc -> Doc

instance Modifies () where
  ascribe () = id

{- | The replacement for `Text.PrettyPrint.<>`.
-}
infixl 6 <.>
(<.>) :: Doc -> Doc -> Doc
(<.>) = (<>)

colored :: Pretty p => Color -> p -> Doc
colored c p = color c (pretty p)

-- | Colorize a `Doc`.
color :: Color -> Doc -> Doc
color c d = zeroWidthText begin <.> d <.> zeroWidthText end
  where
    begin = "\x1b[" ++ toCode c ++ "m"
    end   = "\x1b[0m"

-- | Decorate list of stuff as a tuple.
tuple :: Pretty p => [p] -> Doc
tuple = parens . train ","

-- | Decorate list of stuff as a list.
list :: Pretty p => [p] -> Doc
list = brackets . train ";"

infixr 2 `indent`
-- | First argument is a header to an indented second one.
indent :: Doc -> Doc -> Doc
indent a b = hang a 2 b

infixr 1 `above`
-- | Horisontal composition.
above :: Doc -> Doc -> Doc
above a b = hang a 0 b

-- | Pretty print as a sequence with given separator.
train :: Pretty p => Doc -> [p] -> Doc
train sep' = fsep . punctuate sep' . map pretty

-- | Pretty print as a sequence with given separator.
chain :: Pretty p => Doc -> [p] -> Doc
chain sep' = fsep . map pretty

-- | Pretty print as a vertical block.
block :: Pretty p => [p] -> Doc
block = foldr ($+$) empty . map pretty

-- | For pretty-printing qualified names.
sepByDot :: Pretty p => [p] -> Doc
sepByDot = cat . map (("." <.>) . pretty)

-- | For pretty-printing `Maybe`s.
mb :: Pretty a => (Doc -> Doc) -> Maybe a -> Doc
mb f = maybe empty (f . pretty)

-- | Pretty print as a vertical with elements separated by newline.
sparseBlock :: Pretty a => [a] -> Doc
sparseBlock = vcat . punctuate "\n" . map (($$ empty) . pretty)
