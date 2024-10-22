{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}
module Latlog.Trie (
        Key(..),
        fromList,
        intTrieWild,
        intTrieConcrete,
        curryTrie,
        uncurryTrie,
    ) where

import qualified Data.List as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Functor.Classes
import Text.Show

infixl 8 !

class Key k where
    data Trie k a

    (!) :: Monoid a => Trie k a -> k -> a
    singleton :: Monoid a => k -> a -> Trie k a
    constTrie :: Monoid a => a -> Trie k a
    union :: (a -> a -> a) -> Trie k a -> Trie k a -> Trie k a
    unions :: ([a] -> a) -> [Trie k a] -> Trie k a
    intersect :: (a -> b -> c) -> Trie k a -> Trie k b -> Trie k c
    intersects :: ([a] -> b) -> [Trie k a] -> Trie k b
    tmap :: (a -> b) -> Trie k a -> Trie k b
    project :: Monoid a => Trie k a -> a
    simplify :: Monoid a => (a -> Maybe a) -> Trie k a -> Maybe (Trie k a)

instance Key () where
    newtype Trie () a = UnitTrie a

    UnitTrie x ! () = x
    singleton () x = UnitTrie x
    constTrie x = UnitTrie x
    union f (UnitTrie x) (UnitTrie y) = UnitTrie (f x y)
    unions f ts = UnitTrie $ f [x | UnitTrie x <- ts]
    intersect f (UnitTrie x) (UnitTrie y) = UnitTrie (f x y)
    intersects f ts = UnitTrie $ f [x | UnitTrie x <- ts]
    tmap f (UnitTrie x) = UnitTrie (f x)
    project (UnitTrie x) = x
    simplify f (UnitTrie x) = UnitTrie <$> f x

instance Key Int where
    data Trie Int a = IntTrie a (IntMap a)

    IntTrie w m ! n = w <> IntMap.findWithDefault mempty n m
    singleton n x = IntTrie mempty (IntMap.singleton n x)
    constTrie x = IntTrie x IntMap.empty
    union f (IntTrie x1 m1) (IntTrie x2 m2) = IntTrie (f x1 x2) (IntMap.unionWith f m1 m2)
    unions f ts = IntTrie (f xs) (IntMap.unionsWith (\x y -> f [x, y]) ms)
        where
            (xs, ms) = unzip [(x, m) | IntTrie x m <- ts]
    intersect f (IntTrie x1 m1) (IntTrie x2 m2) = IntTrie (f x1 x2) (undefined)
    intersects f [] = IntTrie (f []) IntMap.empty
    intersects f ts = IntTrie (f xs) ms''
        where
            (xs, ms) = unzip [(x, m) | IntTrie x m <- ts]
            ms' = List.sortOn IntMap.size ms
            ms'' = fmap f . foldr (IntMap.intersectionWith (++)) IntMap.empty $ map (fmap (\x -> [x])) ms'
    tmap f (IntTrie x m) = IntTrie (f x) (fmap f m)
    project (IntTrie x m) = x <> mconcat (IntMap.elems m)
    simplify f (IntTrie x m) = mk (f x) (IntMap.mapMaybe f m)
        where
            mk Nothing m
                | IntMap.null m = Nothing
                | otherwise = Just $ IntTrie mempty m
            mk (Just x) m = Just $ IntTrie x m

instance (Key k1, Key k2) => Key (k1, k2) where
    newtype Trie (k1, k2) a = ProdTrie (Trie k1 (Trie k2 a))

    ProdTrie t ! (k1, k2) = t ! k1 ! k2
    singleton (k1, k2) x = ProdTrie $ singleton k1 (singleton k2 x)
    constTrie x = ProdTrie $ constTrie (constTrie x)
    union f (ProdTrie t1) (ProdTrie t2) = ProdTrie $ union (union f) t1 t2
    unions f ts = ProdTrie $ unions (unions f) [t | ProdTrie t <- ts]
    intersect f (ProdTrie t1) (ProdTrie t2) = ProdTrie $ intersect (intersect f) t1 t2
    intersects f ts = ProdTrie $ intersects (intersects f) [t | ProdTrie t <- ts]
    tmap f (ProdTrie t) = ProdTrie $ tmap (tmap f) t
    project (ProdTrie t) = project (project t)
    simplify f (ProdTrie t) = ProdTrie <$> simplify (simplify f) t

instance (Key k1, Key k2) => Key (Either k1 k2) where
    data Trie (Either k1 k2) a = SumTrie (Trie k1 a) (Trie k2 a)

    SumTrie t1 t2 ! Left k = t1 ! k
    SumTrie t1 t2 ! Right k = t2 ! k
    singleton (Left k) x = SumTrie (singleton k x) mempty
    singleton (Right k) x = SumTrie mempty (singleton k x)
    constTrie x = SumTrie (constTrie x) (constTrie x)
    union f (SumTrie ta1 tb1) (SumTrie ta2 tb2) = SumTrie (union f ta1 ta2) (union f tb1 tb2)
    unions f ts = SumTrie (unions f xs) (unions f ys)
        where
            (xs, ys) = unzip [(x, y) | SumTrie x y <- ts]
    intersect f (SumTrie ta1 tb1) (SumTrie ta2 tb2) = SumTrie (intersect f ta1 ta2) (intersect f tb1 tb2)
    intersects f ts = SumTrie (intersects f xs) (intersects f ys)
        where
            (xs, ys) = unzip [(x, y) | SumTrie x y <- ts]
    tmap f (SumTrie ta tb) = SumTrie (tmap f ta) (tmap f tb)
    project (SumTrie ta tb) = project ta <> project tb
    simplify f (SumTrie ta tb) =
        case (simplify f ta, simplify f tb) of
            (Nothing, Nothing) -> Nothing
            (Nothing, Just tb') -> Just $ SumTrie mempty tb'
            (Just ta', Nothing) -> Just $ SumTrie ta' mempty
            (Just ta', Just tb') -> Just $ SumTrie ta' tb'

instance (Key k, Semigroup a) => Semigroup (Trie k a) where
    (<>) = union (<>)

instance (Key k, Monoid a) => Monoid (Trie k a) where
    mempty = unions mconcat []
    mconcat = unions mconcat

instance (Key k) => Functor (Trie k) where
    fmap = tmap

instance (Key k, Monoid a, Num a) => Num (Trie k a) where
    fromInteger = constTrie . fromInteger
    (+) = union (+)
    (*) = intersect (*)
    negate = tmap negate
    abs = tmap abs
    signum = tmap signum

fromList :: (Key k, Monoid a) => [(k, a)] -> Trie k a
fromList = mconcat . map (uncurry singleton)

intTrieWild :: Trie Int a -> a
intTrieWild (IntTrie x _) = x

intTrieConcrete :: Trie Int a -> IntMap a
intTrieConcrete (IntTrie _ m) = m

curryTrie :: Trie (k1, k2) a -> Trie k1 (Trie k2 a)
curryTrie (ProdTrie t) = t

uncurryTrie :: Trie k1 (Trie k2 a) -> Trie (k1, k2) a
uncurryTrie = ProdTrie

instance Show1 (Trie ()) where
    liftShowsPrec sh _ p (UnitTrie x) = showString "{" . sh 0 x . showString "}"

instance Show1 (Trie Int) where
    liftShowsPrec sh _ p (IntTrie x m) =
        showString "{* → " .
        foldr (.) id (List.intersperse (showString " | ")
            (sh 0 x : [showsPrec 0 k . showString " → " . sh 0 v | (k, v) <- IntMap.toList m])) .
        showString "}"
        -- ("{* → " ++) . List.intercalate " | " (show x : [show k ++ " → " ++ show v | (k, v) <- IntMap.toList m]) ++ "}"

instance (Show1 (Trie k1), Show1 (Trie k2)) => Show1 (Trie (k1, k2)) where
    liftShowsPrec sh sl p (ProdTrie t) = liftShowsPrec (liftShowsPrec sh sl) (liftShowList sh sl) p t

instance (Show1 (Trie k), Show a) => Show (Trie k a) where
    showsPrec = liftShowsPrec showsPrec showList

