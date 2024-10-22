module Latlog.Parser (
        runP,
        pProgram,
        pSentence,
        pTerm,
    ) where

import Control.Monad.Trans
import Data.Char
import Data.Maybe
import Data.STRef
import Data.Map (Map)
import qualified Data.Map as M
import Text.Parsec hiding (runP)

import Latlog.Term

type P s = ParsecT String (Map Name (Hole s)) (T s)

data FixTree s = Simple [Term s] | Binop1 Fixity (Term s) (FixTree s) | Binop Fixity (Term s) (FixTree s) (FixTree s)
    deriving (Show)

runP :: P s a -> String -> T s (Either ParseError a)
runP p s = runParserT (spaces *> p <* eof) M.empty "" s

pProgram :: P s [Term s]
pProgram = many pSentence

pSentence :: P s (Term s)
pSentence = pTerm <* pDot

pTerm :: P s (Term s)
pTerm = do
    terms <- many1 pSimpleTerm
    tree <- buildFixTree terms
    flattenFixTree tree

pSimpleTerm :: P s (Term s)
pSimpleTerm = pParenthesisedTerm <|> (UVar <$> pHole) <|> (Number <$> pNumber) <|> pOp <|> (Atom <$> pAtom) <|> (Dict <$> pTrie)

pParenthesisedTerm :: P s (Term s)
pParenthesisedTerm = between (char '(' >> spaces) (char ')' >> spaces) pTerm

pHole :: P s (Hole s)
pHole = do
    name <- (:) <$> upper <*> many letter
    spaces
    holes <- getState
    case M.lookup name holes of
        Just hole -> pure hole
        Nothing -> do
            hole <- lift $ newHoleId name >>= newEmptyHole
            putState $! M.insert name hole holes
            pure hole

pOp :: P s (Term s)
pOp = (:$) (Atom "@") . Atom <$> (char '@' >> pAtom)

pAtom :: P s Name
pAtom = (many1 letter <|> many1 symbol) <* spaces

pTrie :: P s (Trie s (Term s))
pTrie = fmap trieFromList . between (char '{' >> spaces) (char '}' >> spaces) $ pTrieBinding `sepBy` pComma

pTrieBinding :: P s (Term s, Term s)
pTrieBinding = do
    t <- pTerm
    case t of
        (Atom ":=" :$ t1 :$ t2) -> pure (t1, t2)

pNumber :: P s No
pNumber = (fromInteger <$> pInteger) <|> (string "ω" >> spaces >> pure omega)

pInteger :: P s Integer
pInteger = read <$> ((++) <$> option "" (string "~" >> pure "-") <*> many1 digit <* spaces)

pDot :: P s ()
pDot = string "." *> spaces

pComma :: P s ()
pComma = string "," *> spaces

symbol :: P s Char
symbol = satisfy (\c -> not (elem c "(){}@.,") && (isSymbol c || isPunctuation c))

flattenFixTree :: FixTree s -> P s (Term s)
flattenFixTree (Simple ts) = pure $ foldl1 (:$) ts
flattenFixTree (Binop Arrow (Atom "->") (Simple [Atom x]) tree) = do
    t <- flattenFixTree tree
    pure $ lam x t
flattenFixTree (Binop _ op tree1 tree2) = do
    t1 <- flattenFixTree tree1
    t2 <- flattenFixTree tree2
    pure $ op :$ t1 :$ t2

buildFixTree :: [Term s] -> P s (FixTree s)
buildFixTree [] = fail "empty list"
buildFixTree [t]
    | isNothing (asOp t) = pure $ Simple [t]
buildFixTree (t : ts) = buildFixTree ts >>= insertTerm t 

insertTerm :: Term s -> FixTree s -> P s (FixTree s)
insertTerm t tree =
    case asOp t of
        Nothing -> pure $ insertRegular t tree
        Just f -> insertOp f t tree

insertRegular :: Term s -> FixTree s -> FixTree s
insertRegular t (Simple ts) = Simple (t : ts)
insertRegular t (Binop1 f op tree) = Binop f op (Simple [t]) tree
insertRegular t (Binop f op tree1 tree2) = Binop f op (insertRegular t tree1) tree2

insertOp :: Fixity -> Term s -> FixTree s -> P s (FixTree s)
insertOp f op tree@(Simple _) = pure $ Binop1 f op tree
insertOp f op tree@(Binop1 _ op' _) = fail $ "consecutive binary operators " ++ show op ++ " and " ++ show op'
insertOp f op tree@(Binop f' op' tree1 tree2)
    | f <= f' = pure $ Binop1 f op tree
    | otherwise = Binop f' op' <$> insertOp f op tree1 <*> pure tree2

lam :: Name -> Term s -> Term s
lam x t = Lam (Abs x (abstract x 0 t))

abstract :: Name -> Int -> Term s -> Term s
abstract x j t@(UVar _) = t
abstract x j t@(Var i) = t
abstract x j (t1 :$ t2) = abstract x j t1 :$ abstract x j t2
abstract x j (Lam (Abs y t))
    | x == y = Lam (Abs y t)
    | otherwise = Lam $ Abs y (abstract x (j + 1) t)
abstract x j t@(Atom y)
    | x == y = Var j
    | otherwise = t
abstract x j t@(Number _) = t
