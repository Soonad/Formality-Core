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
type Eras = Bool

data Term
  = Var Int                  -- Variable
  | Ref Name                 -- Reference
  | Typ                      -- Type type
  | All Eras Name Term Term  -- Forall
  | Lam Eras Name Term       -- Lambda
  | App Eras Term Term       -- Application
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

-- Substitution

shift :: Int -> Int -> Term -> Term
shift inc dep term = let go x = shift inc dep x in case term of
  Var i        -> Var (if i < dep then i else (i + inc))
  Ref n        -> Ref n
  Typ          -> Typ
  All e n h b  -> All e n (go h) (shift inc (dep + 1) b)
  Lam e n b    -> Lam e n (shift inc (dep + 1) b)
  App e f a    -> App e (go f) (go a)
  Slf n t      -> Slf n (shift inc (dep + 1) t)
  Ins t x      -> Ins (go t) (go x)
  Eli x        -> Eli (go x)
  Ann d t x    -> Ann d (go t) (go x)

-- substitute a value for an index at a certain depth in a term
subst :: Term -> Int -> Term -> Term
subst v dep term =
  let v'   = shift 1 0 v
      go x = subst v dep x
  in case term of
  Var i       -> if i == dep then v else Var (i - if i > dep then 1 else 0)
  Ref n       -> Ref n
  Typ         -> Typ
  All e n h b -> All e n (go h) (subst v' (dep + 1) b)
  Lam e n b   -> Lam e n (subst v' (dep + 1) b)
  App e f a   -> App e (go f) (go a)
  Slf n t     -> Slf n (subst v' (dep + 1) t)
  Ins t x     -> Ins (go t) (go x)
  Eli x       -> Eli (go x)
  Ann d t x   -> Ann d (go t) (go x)

-- Erase computationally irrelevant terms
erase :: Term -> Term
erase term = let go = erase in case term of
  All e n h b  -> All e n (go h) (go b)
  Lam True n b -> (subst (Ref "<erased>") 0 b) 
  Lam e    n b -> Lam e n (go b)
  App True f a -> go f
  App e    f a -> App e (go f) (go a)
  Slf n t      -> Slf n (go t)
  Ins t x      -> go x
  Eli x        -> go x
  Ann d t x    -> go x
  _            -> term

-- lookup the value of an expression in a module
deref :: Name -> Module -> Term
deref n defs = maybe (Ref n) _term (M.lookup n defs)

-- lower-order interpreter
evalTerm :: Term -> Module -> Term
evalTerm term mod = go term
  where
  go :: Term -> Term
  go t = case t of
    All e n h b -> All e n h b
    Lam e n b   -> Lam e n (go b)
    App e f a -> case go f of
      Lam e n b -> go (subst a 0 b)
      f         -> App e f (go a)
    Ins t x   -> go x
    Eli x     -> go x
    Ann d t x -> go x
    Ref n     -> case (deref n mod) of
      Ref m   -> if n == m then Ref m else go (deref n mod)
      x       -> go x
    _         -> term

data TermH
  = VarH Int
  | RefH Name
  | TypH
  | AllH Eras Name TermH (TermH -> TermH)
  | LamH Eras Name (TermH -> TermH)
  | AppH Eras TermH TermH
  | SlfH Name (TermH -> TermH)
  | InsH TermH TermH
  | EliH TermH
  | AnnH Bool TermH TermH

toTermH :: Term -> TermH
toTermH t = go [] t
  where
    go :: [TermH] -> Term -> TermH
    go vs t = case t of
      Var i       -> if i < length vs then vs !! i else VarH i 
      Ref n       -> RefH n
      Typ         -> TypH
      All e n h b -> AllH e n (go vs h) (\x -> go (x : vs) b)
      Lam e n b   -> LamH e n (\x -> go (x : vs) b)
      App e f a   -> AppH e (go vs f) (go vs a)
      Slf n t     -> SlfH n (\x -> go (x : vs) t)
      Ins t x     -> InsH (go vs t) (go vs x)
      Eli x       -> EliH (go vs x)
      Ann d t x   -> AnnH d (go vs t) (go vs x)

fromTermH :: TermH -> Term
fromTermH t = go 0 t
  where
    go :: Int -> TermH -> Term
    go dep t = case t of
      VarH n       -> Var (dep - n)
      RefH n       -> Ref n
      TypH         -> Typ
      AllH e n h b -> All e n (go dep h) (go (dep + 1) (b $ VarH dep))
      LamH e n b   -> Lam e n (go (dep + 1) (b $ VarH dep))
      AppH e f a   -> App e (go dep f) (go dep a)
      SlfH n t     -> Slf n (go (dep + 1) (t $ VarH dep))
      InsH t x     -> Ins (go dep t) (go dep x)
      EliH x       -> Eli (go dep x)
      AnnH d t x   -> Ann d (go dep t) (go dep x)

reduceTermH :: Module -> TermH -> TermH
reduceTermH defs t = go t
  where
    go :: TermH -> TermH
    go t = case t of
      RefH n       -> case deref n defs of
        Ref m   -> RefH m
        x       -> go (toTermH x)
      LamH True n b   -> (b $ RefH "<erased>") 
      AppH True f a -> go f
      AppH False f a -> case go f of
        LamH e n b -> go (b a)
        f          -> AppH False f (go a)
      InsH t x   -> go x
      EliH x     -> go x
      AnnH d t x -> go x
      _          -> t

normalizeTermH :: Module -> TermH -> TermH
normalizeTermH defs t = go t
  where
    go :: TermH -> TermH
    go t = case t of
      AllH e n h b -> AllH e n (go h) (\x -> go $ b x)
      LamH e n b   -> LamH e n (\x -> go $ b x)
      AppH e f a   -> AppH e (go f) (go a)
      SlfH n t     -> SlfH n (\x -> go $ t x)
      InsH t x   -> go x
      EliH x     -> go x
      AnnH d t x -> go x
      _          -> t

reduce :: Module -> Term -> Term
reduce defs = fromTermH . reduceTermH defs . toTermH

normalize :: Module -> Term -> Term
normalize defs = fromTermH . normalizeTermH defs . toTermH
