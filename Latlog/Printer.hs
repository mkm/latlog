module Latlog.Printer (
        runPrint,
        prProgram,
        prSentence,
        prTerm,
    ) where

import Control.Monad.Reader
import Control.Monad.Writer

import Latlog.Term

type Print s = ReaderT (Fixity, [Name]) (WriterT Output (T s))

newtype Output = Output { fromOutput :: String -> String }

instance Semigroup Output where
    Output f <> Output g = Output (f . g)

instance Monoid Output where
    mempty = Output id

runPrint :: Print s a -> T s String
runPrint p = ($ "") . fromOutput <$> execWriterT (runReaderT p (Lowest, []))

prProgram :: [Term s] -> Print s ()
prProgram = mapM_ prSentence

prSentence :: Term s -> Print s ()
prSentence t = do
    prTerm t
    output ".\n"

prTerm :: Term s -> Print s ()
prTerm (UVar (Hole i _)) = prHoleId i
prTerm (Var i) = varName i >>= output
prTerm (Atom name) = output name
prTerm (Number n) = output (show n)
prTerm (Dict trie) = prTrie trie
prTerm (Lam (Abs x t)) = parens Arrow $ output x >> output " -> " >> withFixity Arrow (withVar x (prTerm t))
prTerm (op :$ t1 :$ t2)
    | Just f <- asOp op = parens f $ withFixity (succ f) (prTerm t1) >> output " " >> withFixity f (prTerm op) >> output " " >> prTerm t2
prTerm (t1 :$ t2) = parens App $ withFixity App (prTerm t1) >> output " " >> withFixity (succ App) (prTerm t2)

prHoleId :: HoleId -> Print s ()
prHoleId (HoleId i "") = output $ show i
prHoleId (HoleId _ name) = output $ name

prTrie :: Trie s (Term s) -> Print s ()
prTrie trie = do
    output "{"
    uncurry prTrieBinding `sepBy` output ", " $ trieToList trie
    output "}"

prTrieBinding :: Term s -> Term s -> Print s ()
prTrieBinding t1 t2 = prTerm (Atom ":=" :$ t1 :$ t2)

sepBy :: (a -> Print s ()) -> Print s () -> [a] -> Print s ()
sepBy f s [] = pure ()
sepBy f s [x] = f x
sepBy f s (x : xs) = f x >> s >> sepBy f s xs

parens :: Fixity -> Print s a -> Print s a
parens f p = do
    f' <- askFixity
    case f < f' of
        True -> do
            output "("
            x <- withFixity Lowest p
            output ")"
            pure x
        False -> p

askFixity :: Print s Fixity
askFixity = fst <$> ask

withFixity :: Fixity -> Print s a -> Print s a
withFixity f = local (\(_, vars) -> (f, vars))

varName :: Int -> Print s Name
varName i = (!! i) . snd <$> ask

withVar :: Name -> Print s a -> Print s a
withVar name = local (\(f, vars) -> (f, name : vars))

output :: String -> Print s ()
output s = tell $ Output (s ++)
