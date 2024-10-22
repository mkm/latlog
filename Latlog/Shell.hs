{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Latlog.Shell (
        Sh,
        runSh,
        execTerm,
        execString,
        execFile,
    ) where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M

import Latlog.Term
import Latlog.Parser
import Latlog.Printer
import Latlog.Eval

type Env = Map Name (Term Pure) 

newtype Sh m a = Sh (StateT Env m a)
    deriving (Functor, Applicative, Monad, MonadIO)

runSh :: Monad m => Sh m a -> m a
runSh (Sh x) = evalStateT x emptyEnv

execTerm :: MonadIO m => Term Pure -> Sh m ()
execTerm (Atom "echo" :$ Atom str) = liftIO . putStrLn $ str
execTerm (Atom "include" :$ Atom file) = execFile (file ++ ".ltg")
execTerm (Atom ":=" :$ nameTerm :$ value) = do
    name <- extractName nameTerm
    addBinding name value
execTerm (Atom "query" :$ query) = do
    env <- getEnv
    runT $ do
        query' <- clone query
        query'' <- makeQuery query'
        query''' <- reduce (\name -> traverse clone $ M.lookup name env) query''
        str <- runPrint $ prTerm query'''
        pure . liftIO . putStrLn $ str
execTerm term =
    liftIO $ print term

execString :: MonadIO m => String -> Sh m ()
execString = parseProgram >=> mapM_ execTerm

execFile :: MonadIO m => String -> Sh m ()
execFile = liftIO . readFile >=> execString

parseProgram :: MonadIO m => String -> Sh m [Term Pure]
parseProgram source =
    case runT $ runP (traverse asPure <$> pProgram) source of
        Left err -> liftIO $ error (show err)
        Right Nothing -> liftIO $ error "not ground"
        Right (Just ts) -> pure ts

makeQuery :: Term s -> T s (Term s)
makeQuery (Lam (Abs x t)) = do
    hole <- newHoleId x >>= newEmptyHole
    let t' = subst 0 (UVar hole) t
    makeQuery t'
makeQuery t = pure t

extractName :: (Monad m) => Term s -> Sh m Name
extractName (Atom name) = pure name
extractName (Atom "@" :$ Atom name) = pure name
extractName term = error $ "not a name: " ++ show term

emptyEnv :: Env
emptyEnv = M.empty

getEnv :: Monad m => Sh m Env
getEnv = Sh get

addBinding :: Monad m => Name -> Term Pure -> Sh m ()
addBinding name value = Sh $ modify (M.insert name value)
