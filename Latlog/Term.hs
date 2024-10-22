{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs, RankNTypes, StandaloneDeriving #-}
module Latlog.Term (
        T,
        Name,
        Fixity(..),
        No,
        Term(..),
        Pure,
        Trie(..),
        TermSet(..),
        Abs(..),
        Hole(..),
        HoleId(..),
        HoleValue(..),
        asOp,
        runT,
        liftST,
        omega,
        newHoleId,
        newEmptyHole,
        getHole,
        putHole,
        fromPure,
        asPure,
        clone,
        termHoles,
        trieFromList,
        trieToList,
        trieEmpty,
        trieSingleton,
        trieUnion,
        trieIntersect,
        trieIntersectSingle,
        tsetEmpty,
    ) where

import Control.Monad.ST
import Control.Monad.State
import Data.STRef
import Data.Either
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

newtype T s a = T { unT :: StateT Int (ST s) a }
    deriving (Functor, Applicative, Monad)

type Name = String

data Fixity
    = Lowest
    | Def
    | Arrow
    | Plus
    | Times
    | Pipe
    | Semicolon
    | In
    | Equal
    | NotEqual
    | App
    | Highest
    deriving (Eq, Ord, Enum, Show)

newtype No = No (Map Integer Integer)
    deriving (Eq)

data Term s
    = UVar (Hole s)
    | Var Int
    | Term s :$ Term s
    | Lam (Abs (Term s))
    | Atom Name
    | Number No
    | Dict (Trie s (Term s))
    deriving (Show)

infixl 9 :$

data Trie s a where
    EmptyM :: Trie s a
    SingleM :: Term s -> a -> Trie s a
    UnionM :: Trie s a -> Trie s a -> Trie s a
    AppM :: Trie s (Trie s a) -> Trie s a
    IntM :: IntMap a -> Trie s a
    deriving (Show)

data TermSet s = Finite (Trie s ()) | Cofinite (Trie s ())
    deriving (Show)

data Abs a = Abs Name a
    deriving (Show)

data HoleId = HoleId !Int Name

data Hole s = Hole HoleId (STRef s (HoleValue s))

type HoleValue s = TermSet s

data Pure
newtype PureTerm = Pure (forall s. Term s)

instance Show No where
    show (No factors)
        | M.null factors = "0"
        | otherwise = intercalate "+" [if e == 0 then show n else show n ++ "ω^" ++ show e | (e, n) <- M.toList factors]

instance Num No where
    fromInteger n = no $ M.singleton 0 n
    No m + No n = no $ M.unionWith (+) m n
    No m * No n = no $ M.fromListWith (+) [(p + q, a * b) | (p, a) <- M.toList m, (q, b) <- M.toList n]
    negate (No m) = No $ M.map negate m
    abs = id
    signum = const 1

instance Show HoleId where
    show (HoleId i name) = show i ++ "?" ++ name

instance Show (Hole s) where
    show (Hole i _) = show i

instance Eq HoleId where
    HoleId i _ == HoleId j _ = i == j

instance Ord HoleId where
    compare (HoleId i _) (HoleId j _) = compare i j

instance Eq (Hole s) where
    Hole i _ == Hole j _ = i == j

instance Ord (Hole s) where
    compare (Hole i _) (Hole j _) = compare i j

asOp :: Term s -> Maybe Fixity
asOp (Atom ":=") = Just Def
asOp (Atom "->") = Just Arrow
asOp (Atom "++") = Just Plus
asOp (Atom "**") = Just Times
asOp (Atom "|") = Just Pipe
asOp (Atom ";") = Just Semicolon
asOp (Atom "in") = Just In
asOp (Atom "=") = Just Equal
asOp (Atom "\\=") = Just NotEqual
asOp _ = Nothing

runT :: (forall s. T s a) -> a
runT m = runST (unT m `evalStateT` 0)

liftST :: ST s a -> T s a
liftST m = T $ lift m

no :: Map Integer Integer -> No
no = No . M.filter (/= 0)

omega :: No
omega = No $ M.singleton 1 1

newHoleId :: Name -> T s HoleId
newHoleId name = T $ do
    i <- get
    put $! i + 1
    pure $ HoleId i name

newEmptyHole :: HoleId -> T s (Hole s)
newEmptyHole i = T $ Hole i <$> lift (newSTRef tsetEmpty)

getHole :: Hole s -> T s (HoleValue s)
getHole (Hole _ ref) = T . lift $ readSTRef ref

putHole :: Hole s -> HoleValue s -> T s ()
putHole (Hole _ ref) x = T . lift $ writeSTRef ref x

fromPure :: PureTerm -> Term s
fromPure (Pure t) = t

asPure :: Term s -> Maybe (Term Pure)
asPure (UVar _) = Nothing
asPure (Var i) = Just $ Var i
asPure (t1 :$ t2) = (:$) <$> asPure t1 <*> asPure t2
asPure (Lam (Abs x t)) = Lam . Abs x <$> asPure t
asPure (Atom a) = Just $ Atom a
asPure (Number n) = Just $ Number n

clone :: Term s -> T s' (Term s')
clone (Var i) = pure $ Var i
clone (t1 :$ t2) = (:$) <$> clone t1 <*> clone t2
clone (Lam (Abs x t)) = Lam . Abs x <$> clone t
clone (Atom a) = pure $ Atom a
clone (Number n) = pure $ Number n

termHoles :: Term s -> T s (Set (Hole s))
termHoles (UVar hole) = pure $ S.singleton hole
termHoles (Var _) = pure S.empty
termHoles (t1 :$ t2) = S.union <$> termHoles t1 <*> termHoles t2
termHoles (Lam (Abs _ t)) = termHoles t
termHoles (Atom _) = pure S.empty
termHoles (Number _) = pure S.empty

asInt :: No -> Maybe Int
asInt (No factors)
    | M.null factors = Just 0
    | [(0, n)] <- M.toList factors, toInteger (fromInteger n) == n = Just $ fromInteger n
asInt _ = Nothing

trieFromList :: [(Term s, a)] -> Trie s a
trieFromList xs = trieFromIntList ns `trieUnion` trieFromGenericList xs'
    where
        (ns, xs') = partitionEithers (map selectInts xs)
        selectInts (Number n, x)
            | Just n' <- asInt n = Left (n', x)
        selectInts (t, x) = Right (t, x)

trieFromIntList :: [(Int, a)] -> Trie s a
trieFromIntList [] = EmptyM
trieFromIntList xs = IntM $ IM.fromList xs

trieFromGenericList :: [(Term s, a)] -> Trie s a
trieFromGenericList = foldr trieUnion EmptyM . map (uncurry SingleM)

trieEmpty :: Trie s a
trieEmpty = EmptyM

trieSingleton :: Term s -> a -> Trie s a
trieSingleton t x = trieFromList [(t, x)]

trieUnion :: Trie s a -> Trie s a -> Trie s a
trieUnion EmptyM t = t
trieUnion t EmptyM = t
trieUnion t1 t2 = t1 `UnionM` t2

trieIntersect :: Monad m => (Term s -> Term s -> m Bool) -> (a -> b -> m c) -> Trie s a -> Trie s b -> m (Trie s c)
trieIntersect unify merge (SingleM k1 v1) t2 = trieIntersectSingle unify (flip merge) t2 k1 v1
trieIntersect unify merge t1 (SingleM k2 v2) = trieIntersectSingle unify merge t1 k2 v2
trieIntersect unify merge (UnionM t1a t1b) t2 = trieUnion <$> trieIntersect unify merge t1a t2 <*> trieIntersect unify merge t1b t2
trieIntersect unify merge t1 (UnionM t2a t2b) = trieUnion <$> trieIntersect unify merge t1 t2a <*> trieIntersect unify merge t1 t2b
trieIntersect unify merge (AppM t1) (AppM t2) = AppM <$> trieIntersect unify (trieIntersect unify merge) t1 t2
trieIntersect unify merge (IntM t1) (IntM t2) = fmap IntM . sequence $ IM.intersectionWith merge t1 t2
trieIntersect _ _ _ _ = pure EmptyM

trieIntersectSingle :: Monad m => (Term s -> Term s -> m Bool) -> (a -> b -> m c) -> Trie s a -> Term s -> b -> m (Trie s c)
trieIntersectSingle unify merge (SingleM k' v') k v = do
    same <- unify k k'
    case same of
        True -> SingleM k <$> merge v' v
        False -> pure EmptyM
trieIntersectSingle unify merge (UnionM ta tb) k v =
    trieUnion <$> trieIntersectSingle unify merge ta k v <*> trieIntersectSingle unify merge tb k v
trieIntersectSingle unify merge (AppM t) (k1 :$ k2) v =
    AppM <$> trieIntersectSingle unify (\t' v' -> trieIntersectSingle unify merge t' k2 v') t k1 v
trieIntersectSingle unify merge (IntM t) (Number k) v =
    case asInt k of
        Nothing -> pure EmptyM
        Just n -> fmap IntM . sequence $ IM.intersectionWith merge t (IM.singleton n v)
trieIntersectSingle unify merge t k v = pure EmptyM

trieToList :: Trie s a -> [(Term s, a)]
trieToList t = trieToListS t []

trieToListS :: Trie s a -> [(Term s, a)] -> [(Term s, a)]
trieToListS EmptyM = id
trieToListS (SingleM k v) = (:) (k, v)
trieToListS (UnionM t1 t2) = trieToListS t1 . trieToListS t2
trieToListS (IntM m) = (++) [(Number $ fromIntegral n, v) | (n, v) <- IM.toList m]

tsetEmpty :: TermSet s
tsetEmpty = Finite trieEmpty
