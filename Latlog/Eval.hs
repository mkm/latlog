{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs, TypeFamilies, RankNTypes, PatternSynonyms, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
module Latlog.Eval (
        E,
    ) where

import Debug.Trace

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.ST
import Data.Proxy
import Data.Maybe
import Data.Foldable
import Data.STRef
import qualified Data.Set as S
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Latlog.Lattice
import Latlog.Trie

newtype No s = No Integer
    deriving (Num, Eq)

data B s where
    B :: No s -> No s -> B s
    BAp :: BHom s -> B s -> B s
    BSum :: Proper a => Term s a -> B s

data BHom s = BHom (B s) (B s)

newtype T s a = T { unT :: StateT Int (ST s) a }
    deriving (Functor, Applicative, Monad)

data E s a
    = E ((B s -> T s a -> T s ()) -> T s ())
    | EEmpty
    | EAlt (E s a) (E s a)
    | EPure (B s) a
    | EHom (BHom s) (E s a)

type EBool s = E s ()
type ESet s a = Term s a -> EBool s

newtype Term s a = Term (STRef s (TermVal s a))
    deriving (Eq)

data TermVal s a = Free | Part (PTerm s a) | Ptr (Term s a)

class Key a => Proper a where
    data PTerm s a

    pground' :: a -> T s (PTerm s a)
    pabsurd' :: T s (PTerm s a)
    enumerate' :: PTerm s a -> E s (PTerm s a)
    asSet' :: PTerm s a -> T s (Trie a (B s))
    unifyPart :: PTerm s a -> PTerm s a -> E s (PTerm s a)
    matchPart :: [(a, EBool s)] -> E s (PTerm s a)
    fromPart :: Trie a (EBool s) -> E s (PTerm s a)
    elimFree :: Term s a -> EBool s
    elimPart :: PTerm s a -> EBool s

    debugPTerm :: PTerm s a -> T s String
    debugPTerm _ = pure "TERM"

ground :: Proper a => a -> E s (Term s a)
ground = liftT . ground'

absurd :: Proper a => E s (Term s a)
absurd = liftT absurd'

ground' :: Proper a => a -> T s (Term s a)
ground' = pground' >=> newTerm . Part

absurd' :: Proper a => T s (Term s a)
absurd' = pabsurd' >>= newTerm . Part

enumerate :: Proper a => Term s a -> EBool s
enumerate t = do
    v <- liftT $ readTerm t
    case v of
        Free -> pure ()
        Ptr t' -> do
            v' <- liftT $ readTerm t'
            bindTerm t v'
            enumerate t
        Part p -> do
            p' <- enumerate' p
            bindTerm t (Part p')

asSet :: (Proper a) => Term s a -> T s (Trie a (B s))
asSet t = do
    v <- readTerm t
    case v of
        Free -> pure $ constTrie (B 1 0)
        Ptr t' -> asSet t'
        Part p -> asSet' p

unify :: Proper a => Term s a -> Term s a -> EBool s
unify t1 t2
    | t1 == t2 = eTrue
    | otherwise = do
        v1 <- liftT $ readTerm t1
        v2 <- liftT $ readTerm t2
        case (v1, v2) of
            (Free, _) -> bindTerm t1 (Ptr t2)
            (_, Free) -> bindTerm t2 (Ptr t1)
            (Ptr r1, _) -> unify r1 t2
            (_, Ptr r2) -> unify t1 r2
            (Part p1, Part p2) -> do
                p <- unifyPart p1 p2
                bindTerm t1 (Ptr t2)
                bindTerm t2 (Part p)

-- match t [] ~ eFalse
-- match t [(x, e)] ~ t "=" x /\ e
-- match t (cs ++ ds) ~ match t cs <|> match t ds
match :: Proper a => Term s a -> [(a, EBool s)] -> EBool s
match t clauses = do
    p <- matchPart clauses
    t' <- liftT $ newTerm (Part p)
    unify t t'

from :: Proper a => Term s a -> Trie a (EBool s) -> EBool s
{-
from t clauses = do
    v <- liftT $ readTerm t
    case v of
        Free -> fromPart clauses >>= bindTerm t . Part
        Ptr r -> from r clauses
-}
from t clauses = do
    p <- fromPart clauses
    t' <- liftT $ newTerm (Part p)
    unify t t'

choose :: Proper a => Term s a -> [a] -> EBool s
choose t xs = from t . fmap sum $ fromList [(x, [eTrue]) | x <- xs]

elim :: Proper a => Term s a -> EBool s
elim t = do
    v <- liftT $ readTerm t
    case v of
        Free -> elimFree t
        Ptr t' -> pure ()
        Part p -> elimPart p

phanterm :: Term s a -> a
phanterm = undefined

debugTerm :: Proper a => Term s a -> T s String
debugTerm t = do
    v <- readTerm t
    case v of
        Free -> pure "_"
        Ptr t' -> debugTerm t'
        Part p -> debugPTerm p

instance Proper () where
    data PTerm s () = PUnit (EBool s)

    pground' () = pure $ PUnit eTrue
    pabsurd' = pure $ PUnit eFalse
    enumerate' (PUnit b) = PUnit eTrue <$ b
    asSet' (PUnit b) = pure $ singleton () (runPureEBool b)
    unifyPart (PUnit b1) (PUnit b2) = pure $ PUnit (b1 /\ b2)
    matchPart clauses = pure . PUnit $ sum [b | ((), b) <- clauses]
    fromPart clauses = pure . PUnit $ project clauses
    elimFree _ = eTrue
    elimPart (PUnit b) = b
    
    debugPTerm (PUnit b) = pure $ "{" ++ show b ++ "}"

instance Proper Int where
    data PTerm s Int = PInt (EBool s) (IntMap (EBool s))

    pground' n = pure . PInt empty $ IntMap.singleton n eTrue
    pabsurd' = pure . PInt eFalse $ IntMap.empty
    enumerate' (PInt w m) = foldr (<|>) (PInt eTrue IntMap.empty <$ w) $ map f (IntMap.toList m)
        where
            f (n, e) = PInt empty (IntMap.singleton n eTrue) <$ e
    asSet' (PInt w m) = pure . mconcat $ constTrie (runPureEBool w) : [singleton n (runPureEBool b) | (n, b) <- IntMap.toList m]
    unifyPart (PInt w1 m1) (PInt w2 m2) = do
        let m = IntMap.intersectionWith (/\) m1 m2
        let ml = fmap (/\ w2) $ IntMap.difference m1 m2
        let mr = fmap (w1 /\) $ IntMap.difference m2 m1
        pure $ PInt (w1 /\ w2) (m `IntMap.union` ml `IntMap.union` mr)
    matchPart = undefined
    -- matchPart clauses = pure . PInt $ IntMap.fromList clauses
    fromPart clauses = pure $ PInt (intTrieWild clauses) (intTrieConcrete clauses)
    elimFree _ = eB (B intCardinality 0)
    elimPart (PInt w m) = eScale intCardinality w <|> fold m

    debugPTerm (PInt w m) = pure $ show w ++ " | " ++ show m

intCardinality = No $ toInteger (maxBound :: Int) - toInteger (minBound :: Int) + 1

instance (Proper a, Proper b) => Proper (a, b) where
    data PTerm s (a, b) = PProd (Term s a) (Term s b)

    pground' (x, y) = PProd <$> ground' x <*> ground' y
    pabsurd' = PProd <$> absurd' <*> absurd'
    enumerate' p@(PProd ta tb) = do
        enumerate ta
        enumerate tb
        pure p
    asSet' (PProd ta tb) = do
        x <- asSet ta
        y <- asSet tb
        pure . uncurryTrie . fmap (\b -> fmap ((/\) b) y) $ x
    unifyPart (PProd ta1 tb1) t2@(PProd ta2 tb2) = do
        unify ta1 ta2
        unify tb1 tb2
        pure t2
    matchPart clauses = do
        ta <- liftT newFreeTerm
        tb <- liftT newFreeTerm
        match ta [(a, match tb [(b, e)]) | ((a, b), e) <- clauses]
        pure $ PProd ta tb
    fromPart clauses = do
        ta <- liftT newFreeTerm
        tb <- liftT newFreeTerm
        from ta $ fmap (from tb) (curryTrie clauses)
        pure $ PProd ta tb
    elimFree t = do
        elimFree (phantomFst t)
        elimFree (phantomSnd t)
    elimPart (PProd ta tb) = do
        elim ta
        elim tb

phantomFst :: Term s (a, b) -> Term s a
phantomFst = undefined

phantomSnd :: Term s (a, b) -> Term s b
phantomSnd = undefined

fstSndPair :: (Proper a, Proper b) => Term s a -> Term s b -> Term s (a, b) -> EBool s
fstSndPair x y xy = do
    t <- liftT $ newTerm (Part (PProd x y))
    t =:= xy

instance (Proper a, Proper b) => Proper (Either a b) where
    data PTerm s (Either a b) = PSum (Term s a) (Term s b)

    pground' (Left x) = PSum <$> ground' x <*> absurd'
    pabsurd' = PSum <$> absurd' <*> absurd'
    enumerate' (PSum ta tb) =
        (absurd >>= \tb' -> PSum ta tb' <$ enumerate ta)
        <|>
        (absurd >>= \ta' -> PSum ta' tb <$ enumerate tb)
    asSet' = undefined
    unifyPart = undefined
    matchPart = undefined
    fromPart = undefined
    elimFree t = elimFree (phantomLeft t) <|> elimFree (phantomRight t)
    elimPart (PSum ta tb) = elim ta <|> elim tb

phantomLeft :: Term s (Either a b) -> Term s a
phantomLeft = undefined

phantomRight :: Term s (Either a b) -> Term s b
phantomRight = undefined

instance Functor (E s) where
    fmap f (E e) = E $ \k -> e $ \b -> k b . fmap f
    fmap f EEmpty = EEmpty
    fmap f (EAlt e1 e2) = EAlt (fmap f e1) (fmap f e2)
    fmap f (EHom bh e) = EHom bh (fmap f e)
    fmap f (EPure b x) = EPure b (f x)

instance Applicative (E s) where
    pure = EPure top
    (<*>) = ap

instance Alternative (E s) where
    empty = EEmpty
    EEmpty <|> e2 = e2
    e1 <|> EEmpty = e1
    e1 <|> e2 = EAlt e1 e2

instance Monad (E s) where
    EEmpty >> _ = EEmpty
    _ >> EEmpty = EEmpty
    e1 >> e2 =
        E $ \k ->
        runE e1 $ \b1 t1 ->
        runE e2 $ \b2 t2 ->
        k (b1 /\ b2) (t1 >> t2)

    EEmpty >>= _ = EEmpty
    -- EAlt e1 e2 >>= f = EAlt (e1 >>= f) (e2 >>= f)
    -- EPure x >>= f = f x
    -- EHom bh e >>= f = EHom bh (e >>= f)
    e >>= f =
        E $ \k ->
        runE e $ \b t ->
        t >>= \x ->
        runE (f x) $ \b' t' ->
        k (b /\ b') t'

instance Semigroup (E s a) where
    (<>) = (<|>)

instance Monoid (E s a) where
    mempty = empty

instance Num (EBool s) where
    fromInteger n = E $ \k -> k (B (fromInteger n) (fromInteger n)) (pure ())
    (+) = (<|>)
    e1 * e2 = E $ \k ->
        runE e1 $ \b t ->
        runE e2 $ \b' t' ->
        k (b * b') (t >> t')
    negate = neg
    abs = eMap $ \(B ns nf) -> B (abs ns) (abs nf)
    signum = eMap $ \(B ns nf) -> B (signum ns) (signum nf)

instance Show a => Show (E s a) where
    show (E _) = "E"
    show EEmpty = "empty"
    show (EAlt e1 e2) = show e1 ++ " <|> " ++ show e2
    show (EPure b x) = "ePure " ++ show b ++ " " ++ show x

instance Semigroup (No s) where
    No x <> No y = No (x + y)

instance Monoid (No s) where
    mempty = No 0

instance Show (No s) where
    show (No n) = show n

instance Semigroup (B s) where
    B s1 f1 <> B s2 f2 = B (s1 <> s2) (f1 <> f2)

instance Monoid (B s) where
    mempty = B mempty mempty

instance Lattice (B s) where
    B s1 f1 /\ B s2 f2 = B (s1 * s2) (s1 * f2 + f1 * s2 + f1 * f2)
    B s1 f1 \/ B s2 f2 = B (s1 * s2 + s1 * f2 + s2 * f1) (f2 * f2)
    neg (B s f) = B f s

instance BoundedLattice (B s) where
    top = B 1 0
    bottom = B 0 1

instance Num (B s) where
    fromInteger n = B (fromInteger n) (fromInteger n)
    B s1 f1 + B s2 f2 = B (s1 + s2) (f1 + f2)
    B s1 f1 * B s2 f2 = B (s1 * s2) (f1 * f2)
    negate (B s f) = B (negate s) (negate f)
    abs (B s f) = B (abs s) (abs f)
    signum (B s f) = B (signum s) (signum f)

instance Show (B s) where
    show (B s f) = show s ++ " ⊕ " ++ show f

simplifyB :: B s -> Maybe (B s)
simplifyB (B 0 0) = Nothing
simplifyB x = Just x

apB :: BHom s -> B s -> B s
apB (BHom (B ss sf) (B fs ff)) (B s f) = B (ss * s + sf * f) (fs * s + ff * f)

runE :: E s a -> (B s -> T s a -> T s ()) -> T s ()
runE (E f) k = f k
runE EEmpty _ = pure ()
runE (EAlt e1 e2) k = do
    runE e1 k
    runE e2 k
runE (EPure b x) k = k b (pure x)
runE (EHom bh e) k = runE e $ \b -> k (bh `apB` b)

runPureEBool :: EBool s -> B s
runPureEBool EEmpty = B 0 0
runPureEBool (EAlt e1 e2) = runPureEBool e1 + runPureEBool e2
runPureEBool (EPure b ()) = b

liftT :: T s a -> E s a
liftT = liftT' (B 1 0)

liftT' :: B s -> T s a -> E s a
liftT' n t = E $ \k -> k n t

liftST :: ST s a -> T s a
liftST m = T $ lift m

eMap :: (B s -> B s) -> E s a -> E s a
eMap f e = E $ \k -> runE e (k . f)

ePure :: B s -> a -> E s a
ePure = EPure

eHom :: BHom s -> E s a -> E s a
eHom bh (EPure b x) = EPure (bh `apB` b) x
eHom bh e = EHom bh e

eScale :: No s -> E s a -> E s a
eScale n = eHom (BHom (B n 0) (B 0 n))

eTrue :: EBool s
eTrue = pure ()

eFalse :: EBool s
eFalse = neg eTrue

eB :: B s -> EBool s
eB b = EPure b ()

eBool :: Bool -> EBool s
eBool False = eFalse
eBool True = eTrue

infix 4 =:=
(=:=) :: Proper a => Term s a -> Term s a -> EBool s
t1 =:= t2 = do
    (eHom (BHom (B 1 (-1)) (B (-1) 1)) $ unify t1 t2) <|> eFalse

eSum :: Proper a => (Term s a -> EBool s) -> EBool s
eSum f = do
    t <- liftT $ newFreeTerm
    f t
    eB (BSum t)

instance Lattice (EBool s) where
    e1 /\ e2 = e1 >> e2
    neg = eHom (BHom (B 0 1) (B 1 0))

instance BoundedLattice (EBool s) where
    top = ePure top ()
    bottom = ePure bottom ()

freeNo :: No s -> No s'
freeNo (No n) = No n

freeB :: B s -> B s'
freeB (B f s) = B (freeNo f) (freeNo s)

expandB :: B s -> EBool s
expandB b@(B _ _) = eB b
expandB (BSum t) = undefined

runE' :: E s a -> (No s -> No s -> T s a -> T s ()) -> T s ()
runE' e k = runE e go
    where
        go (B s f) t = k s f t
        go (BSum x) t = runE' (elim x) $ \s f t' -> k s f (t <* t')

count :: (forall s. EBool s) -> B s'
count e = runT $ do
    result <- liftST $ newSTRef (B 0 0)
    runE' e $ \s f t -> do
        () <- t
        liftST $ modifySTRef' result ((+) (B s f))
    liftST $ freeB <$> readSTRef result

findAll :: Proper a => (forall s. Term s a -> EBool s) -> Trie a (B s')
findAll f = runT $ do
    term <- newFreeTerm
    results <- liftST $ newSTRef []
    let generate = do
        f term
        enumerate term
        liftT $ asSet term
    runE generate $ \b t -> do
        x <- t
        let x' = fmap (\b' -> b /\ b') x
        liftST $ modifySTRef results (x' :)
    fmap freeB . fromMaybe mempty . simplify simplifyB . mconcat <$> liftST (readSTRef results)

runT :: (forall s. T s a) -> a
runT m = runST (unT m `evalStateT` 0)

newTerm :: TermVal s a -> T s (Term s a)
newTerm x = liftST . fmap Term $ newSTRef x

newFreeTerm :: T s (Term s a)
newFreeTerm = newTerm Free

readTerm :: Term s a -> T s (TermVal s a)
readTerm (Term ref) = liftST $ readSTRef ref

writeTerm :: Term s a -> TermVal s a -> T s ()
writeTerm (Term ref) v = liftST $ writeSTRef ref v

bindTerm :: Term s a -> TermVal s a -> EBool s
bindTerm t v = E $ \k -> do
    v' <- readTerm t
    writeTerm t v
    k top $ pure ()
    writeTerm t v'

{-
pattern EmptyA = Atom "empty"
pattern TrueA = Atom "true"
pattern FalseA = Atom "false"
pattern NotA = Atom "not"
pattern PlusPlusA = Atom "++"
pattern TimesTimesA = Atom "**"
pattern SemicolonA = Atom ";"

collect :: E s a -> Context s -> (No -> No -> a -> T s b) -> T s [b]
collect e c f = do
    results <- liftST $ newSTRef []
    runE e c $ \ns nf t -> t >>= f ns nf >>= \y -> liftST $ modifySTRef' results (y :)
    fmap reverse . liftST $ readSTRef results

reduce :: Context s -> Term s -> T s (Term s)
reduce c term = do
    holes <- S.toList <$> termHoles term
    alternatives <- collect (enumerate term) c $ \ns nf () -> do
        constraints <- forM holes $ \hole -> do
            value <- getHole hole
            case value of
                EqualTo term' -> mkEq (UVar hole) <$> normalise term'
                UnequalTo terms -> foldr mkAnd mkTrue <$> mapM (\term' -> mkNeq (UVar hole) <$> normalise term') (trieToList terms)
        let conj = mkPos $ foldr mkAnd mkTrue constraints
        pure $ mkPlus (mkScale ns ns conj) (mkScale nf nf $ mkNot conj)
        -- pure . mkScale ns nf $ foldr mkAnd mkTrue constraints
    pure $ foldr mkPlus mkEmpty alternatives

liftT :: T s a -> E s a
liftT = liftT' 1 0

liftT' :: No -> No -> T s a -> E s a
liftT' ns nf t = E $ \_ k -> k ns nf t

getContext :: E s (Context s)
getContext = E $ \c k -> k 1 0 (pure c)

instance Functor (E s) where
    fmap f e = E $ \c k -> runE e c $ \ns nf -> k ns nf . fmap f

instance Applicative (E s) where
    pure = liftT . pure
    (<*>) = ap

instance Alternative (E s) where
    empty = E $ \_ _ -> pure ()
    e1 <|> e2 = E $ \c k -> do
        runE e1 c k
        runE e2 c k

instance Monad (E s) where
    e >>= f =
        E $ \c k ->
        runE e c $ \ns nf t ->
        t >>= \x ->
        runE (f x) c $ \ns' nf' t' ->
        k (ns * ns') (nf * nf' + nf * ns' + ns * nf') t'

instance MonadPlus (E s) where

success :: E s ()
success = pure ()

failure :: E s ()
failure = eNot success

bindHole :: Hole s -> HoleValue s -> E s ()
bindHole hole value = E $ \_ k -> do
    oldValue <- getHole hole
    putHole hole value
    k 1 0 $ pure ()
    putHole hole oldValue

eNot :: E s a -> E s a
eNot e = E $ \c k -> runE e c (\ns nf -> k nf ns)

eMul :: E s () -> E s () -> E s ()
eMul e1 e2 = E $ \c k ->
    runE e1 c $ \ns1 nf1 t1 ->
    runE e2 c $ \ns2 nf2 t2 ->
    k (ns1 * ns2) (nf1 * nf2) (t1 >> t2)

eExists :: Name -> Term s -> E s ()
eExists x t = do
    hole <- liftT $ newHoleId x >>= newEmptyHole
    let t0 = subst 0 (UVar hole) t
    enumerate t0
    value <- liftT $ getHole hole
    case value of
        EqualTo _ -> pure ()

eNumber :: No -> E s ()
eNumber n = E $ \_ k -> k n n (pure ())

eScale :: No -> No -> E s a -> E s a
eScale ns nf e = E $ \c k -> runE e c $ \ns' nf' -> k (ns * ns') (nf * nf')

split :: E s a -> E s a
split e = E $ \c k -> runE e c (f k)
    where
        f k 0 0 _ = pure ()
        f k 0 nf x = k 0 nf x
        f k ns 0 x = k ns 0 x
        f k ns nf x = k ns 0 x >> k 0 nf x

decide :: E s () -> E s Bool
decide e = E $ \c k -> runE e c $ \ns nf () -> k ns 0 True >> k nf 0 False

enumerate :: Term s -> E s ()
enumerate = whnf >=> enumerateWhnf

enumerateWhnf :: Term s -> E s ()
-- enumerateWhnf EmptyA = empty
enumerateWhnf TrueA = success
-- enumerateWhnf FalseA = failure
enumerateWhnf (NotA :$ t) = eNot $ enumerate t
enumerateWhnf (PlusPlusA :$ t1 :$ t2) = enumerate t1 <|> enumerate t2
enumerateWhnf (TimesTimesA :$ t1 :$ t2) = eMul (enumerate t1) (enumerate t2)
-- enumerateWhnf (Atom "|" :$ t1 :$ t2) = eNot $ eNot (enumerate t1) >> eNot (enumerate t2)
enumerateWhnf (SemicolonA :$ t1 :$ t2) = enumerate t1 >> enumerate t2
enumerateWhnf (Atom "exists" :$ Lam (Abs x t)) = do
    hole <- liftT $ newHoleId x >>= newEmptyHole
    let t0 = subst 0 (UVar hole) t
    enumerate t0
    value <- liftT $ getHole hole
    case value of
        EqualTo _ -> pure ()
        UnequalTo ts -> eScale (omega - fromIntegral (length ts)) 0 success
enumerateWhnf (Atom "=" :$ t1 :$ t2) = unify t1 t2
-- enumerateWhnf (Atom "scale" :$ Number ns :$ Number nf :$ t) = eScale ns nf $ enumerate t
enumerateWhnf (Number n) = eNumber n
enumerateWhnf (Number n :$ t) = eScale n n $ enumerate t
enumerateWhnf t = error $ "not a predicate: " ++ show t

unify :: Term s -> Term s -> E s ()
unify (UVar h) t = unifyHole h t
unify t (UVar h) = unifyHole h t
unify (t1 :$ t2) (t1' :$ t2') = do
    unify t1 t1'
    unify t2 t2'
unify (Atom x) (Atom y)
    | x == y = success
unify (Number x) (Number y)
    | x == y = success
unify _ _ = failure

unifyHole :: Hole s -> Term s -> E s ()
unifyHole h1 (UVar h2)
    | h1 == h2 = success
    | otherwise = do
        v1 <- liftT $ getHole h1
        v2 <- liftT $ getHole h2
        case (v1, v2) of
            (EqualTo t1, EqualTo t2) -> unify t1 t2
            (EqualTo t1, UnequalTo ts2) -> do
                mapM (cleave t1) ts2
                bindHole h2 (EqualTo t1) <|> (bindHole h2 (UnequalTo (t1 : ts2)) >> failure)
            (UnequalTo ts1, EqualTo t2) -> do
                mapM (cleave t2) ts1
                bindHole h1 (EqualTo t2) <|> (bindHole h1 (UnequalTo (t2 : ts1)) >> failure)
            (UnequalTo ts1, UnequalTo ts2) ->
                (bindHole h1 (EqualTo (UVar h2)) >> bindHole h2 (UnequalTo (ts1 ++ ts2)))
                <|>
                (bindHole h1 (UnequalTo (UVar h2 : ts1)) >> bindHole h2 (UnequalTo (UVar h1 : ts2)) >> failure)
unifyHole h t = do
    v <- liftT $ getHole h
    v' <- trieIntersectSingle (\t1 t2 -> decide (unify t1 t2)) (\a b -> pure $ mkAnd a b)
    putHole h v'
    {-
    case v of
        EqualTo t' -> unify t' t
        UnequalTo ts -> do
            mapM (cleave t) (tsetToList ts)
            bindHole h (trieSingleton t) <|> (bindHole h (UnequalTo (trieSingleton t () `trieUnion` ts)) >> failure)
    -}

cleave :: Term s -> Term s -> E s ()
cleave t1 t2 = eNot (unify t1 t2)

normalise :: Term s -> T s (Term s)
normalise (UVar h) = do
    v <- getHole h
    case v of
        Finite ts | [(t, ())] <- trieToList ts -> normalise t
        Cofinite _ -> pure $ UVar h
normalise (t1 :$ t2) = (:$) <$> normalise t1 <*> normalise t2
normalise t@(Atom _) = pure t
normalise t@(Number _) = pure t

whnf :: Term s -> E s (Term s)
whnf (t1 :$ t2) = do
    t1' <- whnf t1
    whnfApp t1' t2
whnf t@(Atom a) = do
    c <- getContext
    r <- liftT $ c a
    maybe (pure t) whnf r
whnf t = pure t

whnfApp :: Term s -> Term s -> E s (Term s)
whnfApp (Lam (Abs _ t)) t' = whnf $ subst 0 t' t
whnfApp t t' = pure (t :$ t')

subst :: Int -> Term s -> Term s -> Term s
subst j t' t@(UVar _) = t
subst j t' t@(Var i)
    | i == j = t'
    | otherwise = t
subst j t' (t1 :$ t2) = subst j t' t1 :$ subst j t' t2
subst j t' (Lam (Abs x t)) = Lam $ Abs x (subst (j + 1) t' t)
subst j t' t@(Atom _) = t
subst j t' t@(Number _) = t

mkEmpty :: Term s
mkEmpty = Atom "empty"

mkTrue :: Term s
mkTrue = Atom "true"

mkFalse :: Term s
mkFalse = Atom "false"

mkNot :: Term s -> Term s
mkNot (Atom "not" :$ t) = t
mkNot (Atom "=" :$ t1 :$ t2) = Atom "\\=" :$ t1 :$ t2
mkNot (Atom "empty") = Atom "empty"
mkNot (Atom "pos" :$ t) = Atom "neg" :$ t
mkNot t = Atom "not" :$ t

mkScale :: No -> No -> Term s -> Term s
mkScale ns nf (Atom "pos" :$ t) = mkScale ns 0 t
mkScale 0 0 t = mkEmpty
mkScale 1 0 t = Atom "pos" :$ t
mkScale 1 1 t = t
mkScale ns nf t
    | ns == nf = Atom "**" :$ Number ns :$ t
    | otherwise = Atom "scale" :$ Number ns :$ Number nf :$ t

mkPos :: Term s -> Term s
mkPos = mkScale 1 0

mkPlus :: Term s -> Term s -> Term s
mkPlus (Atom "empty") t2 = t2
mkPlus t1 (Atom "empty") = t1
mkPlus (Atom "pos" :$ t1) (Atom "pos" :$ t2) = Atom "pos" :$ mkPlus t1 t2
mkPlus t1 t2 = Atom "++" :$ t1 :$ t2

mkAnd :: Term s -> Term s -> Term s
mkAnd t1 (Atom "true") = t1
mkAnd t1 t2 = Atom ";" :$ t1 :$ t2

mkEq :: Term s -> Term s -> Term s
mkEq t1 t2 = Atom "=" :$ t1 :$ t2

mkNeq :: Term s -> Term s -> Term s
mkNeq t1 t2 = mkNot $ mkEq t1 t2
-}
