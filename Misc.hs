module Misc where

import Control.Monad.Reader
import Data.STRef
import Data.Set (Set)
import qualified Data.Set as S

import Latlog.Term
import Latlog.Parser
import Latlog.Printer
import Latlog.Eval
import Latlog.Shell

pp :: String -> String
pp source = runT (runP pTerm source >>= \(Right t) -> runPrint (prTerm t))

ppp :: String -> IO ()
ppp source = runT $ do
    result <- runP pProgram source
    case result of
        Left err -> pure $ print err
        Right ts -> putStrLn <$> runPrint (prProgram ts)

ss :: String -> IO ()
ss source = runT (runP pTerm source >>= \(Right t) -> pure $ print t)

sh :: String -> IO ()
sh src = runSh $ execString ("include std. " ++ src)

run' :: String -> IO ()
run' source = runT (runP pTerm source >>= go)
    where
        go (Left err) = pure $ print err
        go (Right t) = do
            ns <- collect (enumerate t) (\_ -> pure Nothing) $ \ns nf () -> pure (ns, nf)
            pure $ print ns

run :: String -> IO ()
run source = runT (runP pTerm source >>= go)
    where
        go (Left err) = pure $ print err
        go (Right t) = do
            t' <- reduce (\_ -> pure Nothing) t
            p <- runPrint . prTerm $ t'
            pure $ putStrLn p

{-
handle :: STRef s [String] -> Integer -> Term s -> Set (Hole s) -> E s ()
handle _ 0 _ _ = pure ()
handle ref n t holes = do
    s <- concat <$> mapM showHole (S.toList holes)
    liftT . liftST $ modifySTRef' ref (\ss -> ss ++ (show n ++ ":") : s)

showHole :: Hole s -> E s [String]
showHole hole@(Hole i _) = do
    v <- liftT $ getHole hole
    case v of
        EqualTo t -> do
            t' <- normalise t
            p <- liftT . runPrint $ prTerm t'
            pure [show i ++ " = " ++ p]
        UnequalTo [] -> pure []
        UnequalTo ts -> do
            ps <- mapM (liftT . runPrint . prTerm) ts
            pure [show i ++ " \\= " ++ p | p <- ps]

showResult :: Integer -> Term s -> E s String
showResult n t = do
    t' <- normalise t
    p <- liftT . runPrint $ prTerm t'
    pure $ show n ++ " : " ++ p
-}
