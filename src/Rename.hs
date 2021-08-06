
module Rename where

import Control.Applicative
import Data.Traversable
import Data.Functor

import Polysemy
import Polysemy.State hiding (Get)

import Prog

import Debug.Trace

type StackFrame = [(String, Int)]

type Renames (m :: EffectRow) = Members [State [StackFrame], State Int] m

pushName :: Renames m => Name -> Sem m Name
pushName (Name name _) = do
  index <- fresh
  modify @[StackFrame] \(top : stack) -> ((name, index) : top) : stack
  return $ Name name index

updateName :: Renames m => Name -> Sem m Name
updateName (Name "_" _) = pure  "_"
updateName (Name name index) = do
  index' <- gets (find name) <&> maybe index id
  return $ Name name index'

find :: String -> [StackFrame] -> Maybe Int
find n = \case
  []           -> Nothing
  frame : rest -> lookup n frame <|> find n rest

fresh :: Renames m => Sem m Int
fresh = do
  modify @Int (+1)
  get    @Int

locally :: Renames m => Sem m a -> Sem m a
locally act = do
  modify @[StackFrame] ([] :)
  res <- act
  modify @[StackFrame] tail
  return res

withSig :: Renames m => Signature -> (Signature -> Sem m a) -> Sem m a
withSig s k = do
  s' <- renameSig s
  locally do
    s'' <- updateSig s'
    k s''

enterFrame :: Renames m => Sem m ()
enterFrame = modify @[StackFrame] ([] :)

exitFrame :: Renames m => Sem m ()
exitFrame = modify @[StackFrame] tail

class Renamed x where
  rename :: Renames m => x -> Sem m x

instance (Renamed x, Traversable f) => Renamed (f x) where
  rename = traverse rename

instance Renamed Prog where
  rename = \case
    Var name -> Var <$> updateName name
    Lam a    -> Lam <$> rename a
    Pi  a    -> Pi  <$> rename a
    App f x  -> App <$> rename f <*> rename x
    Rec ds   -> Rec <$> rename ds
    New ds   -> New <$> rename ds
    Get x n  -> Get <$> rename x <*> pure n
    Mtc p as -> do
      stack <- get @[StackFrame]
      traceShowM ("Stack", stack)
      Mtc <$> rename p <*> rename as
    Con c t  -> Con c <$> rename t
    Star     -> pure Star
    Hole     -> pure Hole
    LetRec ns bs b -> do
      ns' <- for ns renameSig
      locally do
        LetRec <$> for ns' updateSig <*> rename bs <*> rename b
    Let (Bind s d) b -> do
      withSig s \s' -> do
        Let <$> (Bind s' <$> rename d) <*> rename b
    Ctr n t -> Ctr n <$> rename t

instance Renamed Abstr where
  rename (Abstr s b) = do
    withSig s \s' -> do
      Abstr <$> pure s' <*> rename b

instance Renamed FieldDecl where
  rename (FieldDecl n t) = do
    FieldDecl n <$> rename t

instance Renamed Decl where
  rename = \case
    Bind s b -> do
      withSig s \s' -> do
        Bind <$> pure s' <*> rename b

instance Renamed Alt where
  rename (Alt p b) = do
    locally do
      Alt <$> rename p <*> rename b

instance Renamed Pat where
  rename = \case
    IsVar name      -> IsVar <$> pushName name
    IsCtr name pats -> IsCtr <$> updateName name <*> rename pats
    IsCon c         -> pure $ IsCon c
    As a b          -> As <$> rename a <*> rename b
    Wild            -> pure Wild

renameSig :: Renames m => Signature -> Sem m Signature
renameSig (Signature n t) = Signature n <$> rename t

updateSig :: Renames m => Signature -> Sem m Signature
updateSig (Signature n t) = Signature <$> pushName n <*> pure t

runRename :: Renamed d => d -> d
runRename = run . evalState @[StackFrame] [] . evalState @Int 0 . rename
