
module Infer where

-- import Control.Monad

import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Traversable
import Data.Foldable

import Polysemy
import Polysemy.Reader
import Polysemy.Error
import Polysemy.State hiding (Get)

import Prog
import Rename

type Context = Map.Map Name Type
newtype Subst  = Subst (Map.Map Name Type) deriving newtype (Eq, Ord, Show, Monoid)

instance Semigroup Subst where
  (<>) = subst

data TypeError
  = Occurs Name Type
  | Mismatch Type Type
  | Undefined Name
  | Unexpected String
  | NoField Name Type
  | ExpectedRecord Name Type

die :: Infers m => String -> Sem m a
die = throw . Unexpected

(|-) :: Name -> Prog -> Subst
n |- p = Subst $ Map.singleton n p

(||-) :: [Name] -> [Prog] -> Subst
ns ||- ps = Subst $ Map.fromList $ zip ns ps

without :: Name -> Subst -> Subst
without n (Subst s) = Subst (Map.delete n s)

withoutAll :: [Name] -> Subst -> Subst
withoutAll = flip (foldr without)

type Infers m = Members '[Reader Context, State Int, Error TypeError, State Subst] m

freshVar :: Infers m => String -> Sem m Name
freshVar s = do
  modify @Int (+1)
  i <- get
  return $ Name ("'" ++ s) i

infer :: Infers m => Prog -> Sem m Type
infer prog = do
  sub <- get
  let prog' = subst sub prog
  res <- case prog' of
    Var n -> do
      asks (Map.lookup n) >>= \case
        Just t -> return t
        Nothing -> throw $ Undefined n

    Lam (Abstr (Signature n t) b) -> do
      t' <- normalise' t
      local @Context (Map.singleton n t <>) do
        tb <- infer b
        return $ Pi $ Abstr (Signature n t') tb

    Pi (Abstr (Signature n t) b) -> do
      _ <- infer t
      _ <- infer b
      return Star

    App f x -> do
      ft <- infer f
      xt <- infer x
      r <- freshVar "r"
      n <- freshVar "n"
      unify' ft (Pi (Abstr (Signature n xt) (Var r)))

    Star -> pure Star

    LetRec ns ds b -> do
      ns' <- for ns \(Signature n t) -> do
        t' <- normalise' t
        return $ Signature n t

      let delta = [(n, t) | Signature n t <- ns']

      local @Context (Map.fromList delta <>) do
        for_ (zip ns ds) \(Signature _ t, d) -> do
          t' <- infer d
          unify t t'
        infer b

    Let (Bind (Signature n t) d) b -> do
      t'  <- normalise' t
      td  <- infer d
      t'' <- unify t td
      local @Context (Map.singleton n td <>) do
        infer b

    Rec fs -> do
      for_ fs \(FieldDecl n t) -> do
        infer t
      return Star

    New fs -> do
      fs' <- for fs \(Bind (Signature n t) d) -> do
        t'  <- normalise' t
        td  <- infer d
        t'' <- unify' t' td
        return $ FieldDecl n t''
      return $ Rec fs'

    Get p n -> do
      t <- infer p
      case t of
        Rec fs -> do
          case lookupFieldType n fs of
            Just t -> return t
            Nothing -> throw $ NoField n t
        _ -> throw $ ExpectedRecord n t

    Ctr c t -> do
      normalise' t

    Ctr c t -> do
      normalise' t

    Mtc p alts -> do
      _

    Hole -> do
      Var <$> freshVar "hole"

  normalise res

class Unified p where
  unify :: Infers m => p -> p -> Sem m Subst

instance Unified Prog where
  unify l r = case (l, r) of
    (Var a, Var b)
      | a == b    -> mempty
      | otherwise -> pure $ a |- Var b
    (Var a, b)
      | occurs a b -> throw $ Occurs a b
      | otherwise  -> pure $ a |- b

    (a, Var b)
      | occurs b a -> throw $ Occurs b a
      | otherwise  -> pure $ b |- a

    (Lam a, Lam b) -> unify a b
    (Pi  a, Pi  b) -> unify a b

    (App f x, App g y) -> unify f g <> unify x y

    (Star, Star) -> mempty

    (Let {}, _) -> die $ "unify: Non-reduced let expr - " ++ show l
    (_, Let {}) -> die $ "unify: Non-reduced let expr - " ++ show r

    (LetRec {}, _) -> die $ "unify: Non-reduced let rec expr - " ++ show l
    (_, LetRec {}) -> die $ "unify: Non-reduced let rec expr - " ++ show r

    (Rec fs, Rec gs) -> do
      flip foldMap fs \(FieldDecl n t) -> do
        case lookupFieldType n gs of
          Just u  -> unify t u
          Nothing -> throw $ Mismatch l r

    (New fs, New gs) -> do
      flip foldMap fs \case
        b@(Bind (Signature n _) _) -> do
          case lookupField n gs of
            Just c@Bind  {}  -> unify b c
            _ -> throw $ Mismatch l r

    (Get {}, _) -> die $ "unify: Non-reduced read access expr - " ++ show l
    (_, Get {}) -> die $ "unify: Non-reduced read access expr - " ++ show r

    (Mtc {}, _) -> die $ "unify: Non-reduced pattern matching - " ++ show l
    (_, Mtc {}) -> die $ "unify: Non-reduced pattern matching - " ++ show r

    (Con c t, Con d u) -> do
      if c == d
      then unify t u
      else throw $ Mismatch l r

    (Hole, _) -> mempty
    (_, Hole) -> mempty

    _ -> throw $ Mismatch l r

instance Unified Decl where
  unify l r = case (l, r) of
    (Bind s b, Bind t c) -> unify (Abstr s b) (Abstr t c)

instance Unified Signature where
  unify (Signature _ t) (Signature _ u) = unify t u

lookupFieldType :: Name -> [FieldDecl] -> Maybe Type
lookupFieldType n (FieldDecl n' t : rest)
  | n == n'   = Just t
  | otherwise = lookupFieldType n rest
lookupFieldType _ [] = Nothing

lookupField :: Name -> [Decl] -> Maybe Decl
lookupField n (b@(Bind (Signature n' _) _) : rest)
  | n == n'   = Just b
  | otherwise = lookupField n rest
lookupField _ [] = Nothing

instance Unified Abstr where
  unify (Abstr (Signature n t) b) (Abstr (Signature m u) c) =
    unify u t <> unify b (subst (Subst $ Map.singleton m (Var n)) c)

unify' :: (Infers m) => Prog -> Prog -> Sem m Prog
unify' l r = do
  l' <- normalise' l
  r' <- normalise' r
  sub1 <- unify l' r'
  modify (sub1 <>)
  update l'

update :: (Substituted s, Infers m) => s -> Sem m s
update s = do
  sub <- get
  pure (subst sub s)

normalise' :: (Infers m) => Prog -> Sem m Prog
normalise' p = do
  p' <- update p
  _  <- infer p'
  normalise p'

class Normalised p where
  normalise :: Infers m => p -> Sem m p

instance (Normalised p, Traversable f) => Normalised (f p) where
  normalise = traverse normalise

instance Normalised Prog where
  normalise = \case
    Var n -> pure $ Var n
    Lam a -> Lam <$> normalise a
    Pi  a -> Pi  <$> normalise a
    App f x -> do
      x' <- normalise x
      normalise f >>= \case
        Lam (Abstr (Signature n t) b) -> do
          _ <- normalise t
          pure $ subst (n |- x') b

        f' -> pure $ App f' x'

    Star -> pure Star

    LetRec {} -> do
      die $ "normalise: let rec in type context"

    Let (Bind (Signature n _) d) b -> do
      d' <- normalise d
      pure $ subst (n |- d') b

    Rec fs -> Rec <$> normalise fs
    New fs -> New <$> normalise fs

    Get p n -> do
      p' <- normalise p
      case p' of
        New decls -> do
          case lookupField n decls of
            Just (Bind _ b) -> pure b
            Nothing -> die $ "normalise: cannot reduce - " ++ show (Get p' n)
        _ -> do
          pure $ Get p' n

    Ctr c t -> Ctr c <$> normalise t
    Con c t -> Con c <$> normalise t

    Mtc {} -> do
      die "normalise: cannot pattern match in types yet"

    Hole -> pure Hole

instance Normalised Decl where
  normalise (Bind (Signature n t) b) = do
    t' <- normalise t
    b' <- normalise b
    return $ Bind (Signature n t') b'

instance Normalised FieldDecl where
  normalise (FieldDecl n t) = FieldDecl n <$> normalise t

instance Normalised Abstr where
  normalise (Abstr s b) = Abstr <$> normalise s <*> normalise b

instance Normalised Signature where
  normalise (Signature n t) = Signature n <$> normalise t

occurs :: Substituted s => Name -> s -> Bool
occurs n s = Set.member n (freeVars s)

class Substituted s where
  subst :: Subst -> s -> s
  freeVars :: s -> Set.Set Name

instance (Substituted s, Functor f, Foldable f) => Substituted (f s) where
  subst = fmap . subst
  freeVars = foldMap freeVars

instance Substituted Prog where
  subst sub@(Subst s) = \case
    Var n    -> maybe (Var n) id $ Map.lookup n s
    Lam a    -> Lam (subst sub a)
    Pi  a    -> Pi  (subst sub a)
    App f x  -> App (subst sub f) (subst sub x)
    Star     -> Star
    Rec fs   -> Rec (subst sub fs)
    New fs   -> New (subst sub fs)
    Get p n  -> Get (subst sub p) n
    Mtc p as -> Mtc (subst sub p) (subst sub as)
    Con c t  -> Con c (subst sub t)
    Ctr c t  -> Ctr c (subst sub t)
    Hole     -> Hole
    Let (Bind (Signature n t) d) b -> do
      let t' = subst sub t
      let d' = subst sub d
      let b' = subst (without n sub) b
      Let (Bind (Signature n t') d') b'

    LetRec ns ds b -> do
      let names = map sigName ns
      let types = map sigType ns
      let ns' = zipWith Signature names (subst sub types)
      let sub' = withoutAll names sub
      let ds' = subst sub' ds
      let b' = subst sub' b
      LetRec ns' ds' b'

  freeVars = \case
    Var n -> Set.singleton n
    Lam a -> freeVars a
    Pi  a -> freeVars a
    App f x -> freeVars f <> freeVars x
    Star -> mempty
    Rec fs -> freeVars fs
    New fs -> freeVars fs
    Get p _ -> freeVars p
    Mtc p as -> freeVars p <> freeVars as
    Con _ t -> freeVars t
    Ctr _ t -> freeVars t
    Hole -> mempty
    Let (Bind (Signature n t) d) b ->
      freeVars t <> freeVars d <> Set.delete n (freeVars b)
    LetRec ns ds b ->
      freeVars (map sigType ns)
      <> foldr Set.delete (freeVars ds <> freeVars b) (map sigName ns)

instance Substituted Abstr where
  subst sub (Abstr (Signature n t) b) = do
    let t' = subst sub t
    let b' = subst (without n sub) b
    Abstr (Signature n t') b'

  freeVars (Abstr (Signature n t) b) =
    freeVars t <> Set.delete n (freeVars b)

instance Substituted FieldDecl where
  subst sub (FieldDecl n t) = do
    FieldDecl n (subst sub t)

  freeVars (FieldDecl _ t) =
    freeVars t

instance Substituted Decl where
  subst sub = \case
    Bind (Signature n t) b -> do
      let t' = subst sub t
      let b' = subst (without n sub) b
      Bind (Signature n t') b'

  freeVars = \case
    Bind  (Signature n t) b -> freeVars t <> Set.delete n (freeVars b)

instance Substituted Alt where
  subst sub (Alt pat b) = do
    let names = allPatNames pat
    let b' = subst (withoutAll names sub) b
    Alt pat b'

  freeVars (Alt p b) =
    foldr Set.delete (freeVars b) (allPatNames p)

instance Substituted Subst where
  subst (Subst s1) (Subst s2) =
    Subst $ Map.union s1 (Map.map (subst (Subst s1)) s2)

  freeVars (Subst s) = foldr Set.delete (freeVars s) (Map.keys s)

allPatNames :: Pat -> [Name]
allPatNames = \case
  IsVar n    -> [n]
  IsCtr _ ps -> ps >>= allPatNames
  IsCon {}   -> []
  As    a b  -> [a, b] >>= allPatNames
  Wild       -> []

test =
  let_
    [ "const" =: ("A", Star) --> ("B", Star) --> ("a", "A") --> ("b", "B") --> "a"
    , "id" =: ("A", Star) --> ("a", "A") --> "a"
    , ">>>" =:
        ("A", Star) -->
        ("B", Star) -->
        ("C", Star) -->
        ("f", ("_", "B") ==> "C") -->
        ("g", ("_", "A") ==> "D") -->
        ("x", "A") -->
          "f" <| ("g" <| "x")
    , "List"  =: Ctr "List" (("A", Star) ==> Star)
    , "Nil"   =: Ctr "Nil"  (("A", Star) ==> "List" <| "A")
    , "Cons"  =: Ctr "Cons" (("A", Star) ==> ("_", "A") ==> ("_", "List" <| "A") ==> "List" <| "A")
    ]
  $ Mtc (("const" <| "id") <| Con "1" "Int")
    [ Alt (IsCtr "Cons" ["foo" `As` "bar", IsCtr "Just" ["x"], IsCtr "Nil" []] `As` "w" `As` "q") "bar"
    ]
