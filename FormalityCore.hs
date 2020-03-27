module FormalityCore where

import Data.List hiding (all)
import Data.Maybe
import qualified Data.Map.Strict as M

import Control.Applicative
import Control.Monad
import Data.Foldable hiding (all)

import Prelude hiding (all, mod)

type Name = String
type Done = Bool

data Term
  = Var Int                  -- Variable
  | Ref Name                 -- Reference
  | Typ                      -- Type type
  | All Bool Name Term Term  -- Forall
  | Lam Bool Name Term       -- Lambda
  | App Bool Term Term       -- Application
  | Slf Name Term            -- Self-type
  | Ins Term Term            -- Self-type introduction
  | Eli Term                 -- Self-type elimination
  | Ann Bool Term Term       -- Type annotation
  deriving (Eq, Show, Ord)

data Def = Def { _name :: Name, _type :: Term, _term :: Term } deriving Show

type Module = M.Map Name Def

data Parser a = Parser { runParser :: String -> Maybe (String, a) }

type Vars = [Name]

instance Functor Parser where
  fmap f p = Parser $ \i -> case runParser p i of
    Just (i', a) -> Just (i', f a)
    Nothing      -> Nothing

instance Applicative Parser where
  pure a       = Parser $ \i -> Just (i, a)
  (<*>) fab fa = Parser $ \i -> case runParser fab i of
    Just (i', f) -> runParser (f <$> fa) i'
    Nothing      -> Nothing

instance Alternative Parser where
  empty     = Parser $ \i -> Nothing
  (<|>) a b = Parser $ \i -> case runParser a i of
    Just (i', x) -> Just (i', x)
    Nothing      -> runParser b i

instance Monad Parser where
  return a  = Parser $ \i -> Just (i, a)
  (>>=) p f = Parser $ \i -> case runParser p i of
    Just (i', a) -> runParser (f a) i'
    Nothing      -> Nothing

instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

isSpace :: Char -> Bool
isSpace c = c `elem` " \t\n"

isName :: Char -> Bool
isName c = c `elem` (['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "_")

choice :: [Parser a] -> Parser a
choice = asum

takeWhileP :: (Char -> Bool) -> Parser String
takeWhileP f = Parser $ \i -> Just (dropWhile f i, takeWhile f i)

space :: Parser String
space = takeWhileP isSpace

string :: String -> Parser String
string str = Parser $ \i -> case stripPrefix str i of
  Just i' -> Just (i', str)
  Nothing -> Nothing

sym :: String -> Parser String
sym s = string s <* space

opt :: Char -> Parser Bool
opt c = isJust <$> optional (string (c:[]))

nam :: Parser String
nam = do
  n <- takeWhileP isName
  case n of
    "" -> empty
    _  -> return n

par :: Vars -> Parser Term
par vs = string "(" >> space >> trm vs <* space <* string ")"

all :: Vars -> Parser Term
all vs = do
  n <- sym "(" >> nam <* space
  t <- sym ":" >> trm vs <* space
  e <- opt ';' <* space <* sym ")"
  b <- sym "->" >> trm (n : vs)
  return $ All e n t b

lam :: Vars -> Parser Term
lam vs = do
  n <- sym "(" >> nam <* space
  e <- opt ';' <* space <* sym ")"
  b <- sym "=>" >> trm (n : vs)
  return $ Lam e n b

var :: Vars -> Parser Term
var vs = (\n -> maybe (Ref n) Var (elemIndex n vs)) <$> nam

typ :: Parser Term
typ = string "Type" >> return Typ

slf :: Vars -> Parser Term
slf vs = do
  n <- sym "#{" >> nam <* space <* sym "}"
  t <- trm (n : vs)
  return $ Slf n t

ins :: Vars -> Parser Term
ins vs = Ins <$> (sym "#inst{" >> trm vs <* sym "}") <*> trm vs

eli :: Vars -> Parser Term
eli vs = sym "#elim{" >> trm vs <* sym "}"

app :: Vars -> Term -> Parser Term
app vs f = foldl (\t (a,e) -> App e t a) f <$> (some $ arg vs)
  where
  arg vs = (,) <$> (sym "(" >> trm vs) <*> (opt ';' <* space <* string ")")

ann :: Vars -> Term -> Parser Term
ann vs x = do
  space >> sym "::"
  t <- trm vs
  return $ Ann False t x

trm :: Vars -> Parser Term
trm vs = do
  t <- choice [ all vs, lam vs, typ, slf vs, eli vs, ins vs, var vs, par vs]
  t <- app vs t <|> return t
  ann vs t <|> return t

parseTerm :: String -> Maybe Term
parseTerm str = snd <$> runParser (trm []) str

def :: Parser Def
def = Def <$> (nam <* space) <*> (sym ":" >> trm []) <*> (space >> trm [])

mod :: Parser Module
mod = M.fromList <$> fmap (\d -> (_name d, d)) <$> many (def <* space)

testString1 = intercalate "\n"
  [ "identity : (A : Type) -> (a : A) -> A"
  , "(A) => (a) => a"
  , ""
  , "const : (A : Type) -> (a : A) -> (b : B) -> B"
  , "(A) => (a) => (b) => B"
  , ""
  , "apply_twice : (A : Type) -> (f : (x : A) -> A) -> (x : A) -> A"
  , "(A) => (f) => (x) => f(f(x))"
  ]


stringifyTerm :: Term -> String
stringifyTerm t = go [] t
  where
  cat = concat
  go :: Vars -> Term -> String
  go vs t = case t of
    Var i       -> vs !! i
    Ref n       -> n
    Typ         -> "Type"
    All e n h b -> if e then cat ["(", n, " : ", go vs h, ";) -> ", go (n:vs) b]
                        else cat ["(", n, " : ", go vs h,  ") -> ", go (n:vs) b]
    Lam e n b   -> if e then cat ["(", n, ";) => ", go (n:vs) b]
                        else cat ["(", n,  ") => ", go (n:vs) b]
    App e f a   -> if e then cat ["(", go vs f, ")(", go vs a, ";)"]
                        else cat ["(", go vs f, ")(", go vs a, ")"]
    Slf n t        -> cat ["#{", n, "}", go (n:vs) t]
    Ins t x        -> cat ["new(", go vs t, ")", go vs x]
    Eli x          -> cat ["use(", go vs x, ")"]
    Ann d x y      -> cat [go vs y, " :: ", go vs x]

stringifyDef :: Def -> String
stringifyDef (Def n t d) = 
  concat [n," : ", stringifyTerm t, "\n", stringifyTerm d]

stringifyMod :: Module -> String
stringifyMod = foldl (\s d -> s ++ "\n\n" ++ stringifyDef d) ""
