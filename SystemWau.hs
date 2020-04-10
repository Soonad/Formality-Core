{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingVia #-}
module SystemWau where

import           Data.Bits           (Bits, shiftL, shiftR, xor, (.&.))
import           Data.Char           (ord)
import           Data.Foldable       hiding (all, find)
import           Data.List           hiding (all, find, union)
import qualified Data.Map.Strict     as M
import           Data.Maybe
import           Data.Word

import           Control.Monad.ST
import           Data.STRef

import           Data.Maybe

import           Data.Map            (Map)
import qualified Data.Map            as Map

import           Control.Applicative
import           Control.Monad

import           Prelude             hiding (all, mod)

-- System-ϝ types
-- ====================

type Name = String
type Done = Bool   -- Annotation flag
type Eras = Bool   -- Erasure mark

data Term
  = Var Int Int Name              -- <number>.<number>           Variable
  | Ref Name                      -- <name>                      Reference
  | Typ                           -- Type                        Type of type
  | Mu  Name Term                 -- (μ <name>. <term>)          recursion
  | All Eras Name Name Term Term  -- (∀ <name> : <term>. <term>) Forall
  | Lam Eras Name Term            -- (λ <name>. <term>)          Lambda
  | App Eras Term Term            -- (<term> <term>)             Application
  | Let Name Term Term            -- (let <name> <term> <term>)  Let expression
  | Ann Bool Term Term            -- (: <term> <term>)           Annotation
  deriving (Eq,Ord)

-- "femtoparsec" parser combinator library
-- =======================================

-- a parser of things is function from strings to
-- perhaps a pair of a string and a thing
data Parser a = Parser { runParser :: String -> Maybe (String, a) }

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

choice :: [Parser a] -> Parser a
choice = asum

takeWhileP :: (Char -> Bool) -> Parser String
takeWhileP f = Parser $ \i -> Just (dropWhile f i, takeWhile f i)

takeWhile1P :: (Char -> Bool) -> Parser String
takeWhile1P f = Parser $ \i -> case i of
  (x : xs) -> if f x then runParser (takeWhileP f) i else Nothing
  _        -> Nothing

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser $ \i -> case i of
  (x:xs) -> if f x then Just (xs, x) else Nothing
  _       -> Nothing

anyChar :: Parser Char
anyChar = satisfy (const True)

manyTill :: Parser a -> Parser end -> Parser [a]
manyTill p end = go
  where
    go = ([] <$ end) <|> ((:) <$> p <*> go)

skipMany :: Parser a -> Parser ()
skipMany p = go
  where
    go = (p *> go) <|> pure ()

skipSome :: Parser a -> Parser ()
skipSome p = p *> go
  where
    go = (p *> go) <|> pure ()

string :: String -> Parser String
string str = Parser $ \i -> case stripPrefix str i of
  Just i' -> Just (i', str)
  Nothing -> Nothing

-- System-Wau parser
-- =====================

-- is a space character
isSpace :: Char -> Bool
isSpace c = c `elem` " \t\n"

-- is a name character
isName :: Char -> Bool
isName c = c `elem` (['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ symbols)
  where
    symbols = "_!#$%&*[]?\"'+=|-<>`~"

-- consume whitespace
whitespace :: Parser ()
whitespace = takeWhile1P isSpace >> return ()

-- parse // line comments
lineComment :: Parser ()
lineComment =
  choice
    [ sym "//" >> takeWhileP (/= '\n') >> return ()
    , sym "--" >> takeWhileP (/= '\n') >> return ()
    ]

-- parse `/* */` block comments
blockComment :: Parser ()
blockComment =
  choice
    [ string "/*" >> manyTill anyChar (string "*/") >> return ()
    , string "{-" >> manyTill anyChar (string "-}") >> return ()
    ]

-- space and comment consumer
space :: Parser ()
space = skipMany $ choice [whitespace, lineComment, blockComment]

-- parse a symbol (literal string followed by whitespace or comments)
sym :: String -> Parser String
sym s = string s <* space

data Bind = VarB Name Int | RefB Name deriving Eq
type Ctx = [Bind]

-- parse a valid name, non-empty
nam :: Parser String
nam = do
  n <- takeWhile1P isName
  if n `elem` ["let"] then empty else return n

-- Parses the type of types, `Type`
typ :: Parser Term
typ = string "Type" >> return Typ

-- Parses a dependent function value
lam :: Int -> Ctx -> Parser Term
lam d vs = do
  string "λ"
  (optional space)
  (bodyDepth, bodyCtx, bs) <- binds d vs []
  space
  body <- trm bodyDepth bodyCtx
  return $ foldl (\b (e,n) -> Lam e n b) body bs
  where
    binds :: Int -> Ctx -> [(Eras,Name)]
          -> Parser (Int, Ctx, [(Eras,Name)])
    binds d vs hs = do
      n <- nam
      e <- maybe False id <$> 
             (optional $ (string ";" >> return True)
                     <|> (string "," >> return False))
      space
      let vs' = (VarB n d):vs
      let d' = d + 1
      let hs' = (e,n):hs
      (string "." >> return (d',vs',hs')) <|> (binds d' vs' hs')

all :: Int -> Ctx -> Parser Term
all d vs = do
  s  <- maybe "" id <$> (optional $ nam <* string "@")
  string "∀"
  (optional space)
  (bodyDepth, bodyCtx, bs) <- binds d vs s []
  space
  body <- trm bodyDepth bodyCtx
  return $ foldl (\b (e,s,n,t) -> All e s n t b) body bs
  where
    binds :: Int -> Ctx -> Name -> [(Eras,Name,Name,Term)]
          -> Parser (Int, Ctx, [(Eras,Name,Name,Term)])
    binds d vs s hs = do
      n <- nam <* space <* sym ":"
      let vs' = (VarB s d):vs
      let d' = d + 1
      t <- trm d' vs'
      e <- maybe False id <$> 
             (optional $ (string ";" >> return True)
                     <|> (string "," >> return False))
      space
      let vs'' = (VarB n d'):vs'
      let d'' = d + 2
      let hs' = (e,s,n,t):hs
      (string "." >> return (d'',vs'',hs')) <|> (binds d'' vs'' "" hs')

-- Parses variables, `<name>`
var :: Int -> Ctx -> Parser Term
var d vs = do
  c <- length <$> many (string "^")
  n <- nam
  return $ go vs c 0 n
  where
    go (x:xs) cs varIndex n
      | VarB m d <- x, n == m, cs == 0 = Var varIndex d n
      | VarB m d <- x, n == m          = go xs (cs - 1) (varIndex + 1) n
      | VarB m d <- x, n /= m          = go xs cs (varIndex + 1) n
      | RefB m <- x, n == m, cs == 0   = Ref n
      | RefB m <- x, n == m            = go xs (cs - 1) varIndex n
      | otherwise                      = go xs cs varIndex n
    go [] cs varIndex n                = Ref n 

-- A recursive term. TODO: reject non-unique names
mu :: Int -> Ctx -> Parser Term
mu d vs = do
  n <- string "μ" >> (optional space) >> nam <* sym "."
  if ((RefB n) `elem` vs) then do empty
  else do
    b <- trm d ((RefB n):vs)
    return $ Mu n b

app :: Int -> Ctx -> Parser Term
app d vs = foldl (\t (a,e) -> App e t a) <$> arg <*> (some args) <* string ")"
  where
  arg  = string "(" >> trm d vs <* space
  args = (,) <$> (space >> trm d vs)
             <*> (maybe False (const True) <$> optional (string ";"))

ann :: Int -> Ctx -> Parser Term
ann d vs = do
  sym ":"
  t <- trm d vs
  space >> (optional $ sym ";")
  x <- trm d vs
  return $ Ann False t x

let_ d vs = do
  n <- sym "let" >> nam <* space
  x <- trm d vs <* space <* (optional $ sym ";")
  b <- trm (d+1) ((VarB n d):vs)
  return $ Let n x b

par :: Int -> Ctx -> Parser Term
par d vs = string "(" >> space >> trm d vs <* space <* string ")"

-- Parses a term
trm :: Int -> Ctx -> Parser Term
trm d vs = choice 
  [ all d vs
  , let_ d vs
  , lam d vs
  , var d vs
  , mu d vs
  , typ
  , app d vs
  , par d vs
  , ann d vs
  ]


parseTerm :: String -> Maybe Term
parseTerm str = snd <$> runParser (trm 0 []) str

testString1 = intercalate "\n"
  [ "let identity : ∀A:Type a:A. a"
  , "  λA a. a"
  , "let const : ∀A:Type a:A b:B. B"
  , "  λA a b. a"
  , "let apply_twice : ∀A:Type, f:(∀x:A. A), x:A. A"
  , "  λA f x. (f (f x));"
  , "main"
  ]

-- pretty-printing
-- ===================================

instance Show Term where
  show t = pretty True t

pretty :: Bool -> Term -> String
pretty indices t = case t of
  Var i a n      -> if indices then cat [n,".",show i, ".", show a] else n
  Ref n          -> n
  Typ            -> "Type"
  Mu n b         -> cat ["μ",n,".", go b]
  All e "" n t b -> cat ["∀",goAll e n t b]
  All e s n t b  -> cat [s,"@∀",goAll e n t b]
  Lam e n b      -> cat ["λ",goLam e n b]
  App e f a      -> cat ["(", goApp e f a, ")"]
  Let n x b      -> cat ["let ",n," ",go x,";\n", go b]
  Ann d x y      -> cat ["(: ", go x,"; ",go y,")"]

  where
    go = pretty indices
    cat = concat
    era e x y = if e then x else y
    era' e = era e "; " ", "
    goAll e n t b = case b of
      All e' "" n' t' b' -> cat [n,":",go t,era' e, goAll e' n' t' b']
      _                  -> cat [n,":",go t,era e ";. " ". ", go b]

    goApp e f a = case f of
      App e' f' a' -> cat [goApp e' f' a', " ", go a, era e ";" ""]
      _            -> cat [go f, " ", go a, era e ";" ""]

    goLam e n b = case b of
      Lam e' n' b' -> cat [n, era e "; " " ", goLam e' n' b']
      _            -> cat [n, era e ";. " ". ", go b]

parsePretty :: Bool -> String -> IO ()
parsePretty b str = case runParser (trm 0 []) str of
  Nothing     -> putStrLn ""
  Just ("",x) -> putStrLn $ pretty b x

parseTerm' :: String -> Term
parseTerm' = fromJust . parseTerm

-- Substitution
-- ============

-- shift all indices by an increment above a depth in a term
shift :: Int -> Int -> Int -> Term -> Term
shift d 0 _ term     = term
shift d inc dep term = let go n x = shift (d + n) inc (dep + n) x in case term of
  Var i a n     -> let i' = if i < dep then i else (i + inc)
                    in Var i' (d - i') n
  Ref n         -> Ref n
  Typ           -> Typ
  Mu  n b       -> Mu n (go 0 b)
  All e s n h b -> All e s n (go 1 h) (go 2 b)
  Lam e n b     -> Lam e n (go 1 b)
  App e f a     -> App e (go 0 f) (go 0 a)
  Let n x b     -> Let n (go 0 x) (go 1 b)
  Ann d t x     -> Ann d (go 0 t) (go 0 x)

-- substitute a value for an index at a certain depth in a term
subst :: Int -> Term -> Int -> Term -> Term
subst d v dep term = let go n x = subst (d + n) (shift d n 0 v) (dep + n) x in
  case term of
    Var i a n     -> if i == dep then v else
      let i' = i - if i > dep then 1 else 0
      in Var i' (d - i' - 1) n
    Ref n         -> Ref n
    Mu  n b       -> Mu n (go 0 b)
    Typ           -> Typ
    All e s n h b -> All e s n (go 1 h) (go 2 b)
    Lam e n b     -> Lam e n (go 1 b)
    App e f a     -> App e (go 0 f) (go 0 a)
    Let n x b     -> Let n (go 0 x) (go 1 b)
    Ann d t x     -> Ann d (go 0 t) (go 0 x)

-- Evaluation
-- ==========

-- Erase computationally irrelevant terms
erase :: Int -> Term -> Term
erase d term = let go n = erase (d + n); in case term of
  All e s n t b -> All e s n (go 1 t) (go 2 b)
  Lam True n b  -> subst d (Ref "<erased>") 0 b
  Lam e n b     -> Lam e n (go 1 b)
  App True f a  -> go 0 f
  App e f a     -> App e (go 0 f) (go 0 a)
  Let n x b     -> Let n (go 0 x) (go 0 b)
  Ann c t x     -> go 0 x
  _             -> term

substRef :: Int -> Term -> Name -> Term -> Term
substRef d v n term = case term of
  Ref m         -> if n == m then v else Ref m
  All e s n t b -> All e s n (go 1 t) (go 2 b)
  Lam e n b     -> Lam e n (go 1 b)
  App e f a     -> App e (go 0 f) (go 0 a)
  Mu  n b       -> Mu n (go 0 b)
  Let n x b     -> Let n (go 0 x) (go 1 b)
  Ann c t x     -> Ann c (go 0 t) (go 0 x)
  _             -> term
  where
    go k t = substRef (d + k) (shift d k 0 v) n t


-- reduce one step of term
reduce :: Term -> Term
reduce term = go 0 term
  where
  go :: Int -> Term -> Term
  go d t = case t of
    Lam e n b     -> Lam e n (go (d+1) b)
    App e f a     -> case go d f of
      Lam e n b -> go d (subst d a 0 b)
      f         -> App e f (go d a)
    Ann  _ t x  -> go d x
    Let  n x b  -> subst d x 0 b
    Mu n b      -> substRef d (Mu n b) n b
    _           -> t

whnf :: Term -> Term
whnf term = go [] term
  where
  go :: [(Eras,Term)] -> Term -> Term
  go apps t = case t of
    App e f a     -> go ((e,a) : apps) f
    Lam e n b     -> case apps of
      []     -> Lam e n b
      ((e,a):as) -> go as (subst 0 a 0 b)
    Ann  _ t x  -> go apps x
    Let  n x b  -> go apps (subst 0 x 0 b)
    Mu n b      -> go ((fmap whnf) <$> apps) (substRef 0 (Mu n b) n b)
    _           -> foldl (\t (e,a) -> App e t a) t apps

test2 :: String
test2 = intercalate "\n"
  [ "let a μx. λy. (y x);"
  , "a"
  ]

test3 :: String
test3 = intercalate "\n"
  [ "let a λz. μx. λy. (z x);"
  , "a"
  ]
test4 :: String
test4 = intercalate "\n"
  [ "let a b;"
  , "let identity  λA a. a;"
  , "(identity a)"
  ]

data BohmTree = BohmRoot Term BohmTree BohmTree

bohmTree :: Term -> Tree

--naiveBohm :: Term -> Term -> Bool
--naiveBoh a b = 

-- Union Find
-- ===========

-- An lightweight implementation of Tarjan's Union-Find algorithm.
-- This is a port of the /equivalence/ package and uses mutable
-- references.

-- Each equivalence class has one member, or root, that serves as its
-- representative element. Every element in the class is either the root
-- (distance 0), points directly to the root (distance 1), 
-- or points to an element with a smaller distance to the root.
--
-- Therefore, whenever we want to test whether two elements are in the same
-- class, we follow their references until we hit their roots, and then compare
-- their roots for equality.
--
-- This algorithm performs lazy path compression. Whenever we traverse a path 
-- containing nodes with a distance from root > 1, once we hit the root we
-- update all the nodes in that path to point to the root directly:
--
-- *           *
-- |         /   \
-- a   =>   a     b
-- |
-- b

-- Additionally, when we merge two classes via `union`, the root of the smaller
-- class will point to the root of the larger
--
-- *1      *2           *2
-- |   +   |    =>    /  |
-- a       b         *1  b
--         |         |   |
--         c         a   c


-- A reference to a node
newtype NRef s a = NRef { _ref :: STRef s (Node s a) } deriving Eq

-- A Node is either root or a link
data Node s a
  = Root {_value :: a, _weight :: Int}
  | Node {_value :: a, _parent :: NRef s a}

-- An equivalence relation is a reference to a map of elements to node references
data Equiv s a = Equiv {_elems :: STRef s (Map a (NRef s a))}

-- A new equivalence relation
newEquiv :: Ord a => ST s (Equiv s a)
newEquiv = Equiv <$> (newSTRef M.empty)

-- create a new class in a relation with a value as root
singleton :: Ord a => Equiv s a -> a -> ST s (NRef s a)
singleton eq val = do
  root <- NRef <$> newSTRef (Root {_value = val, _weight = 1})
  modifySTRef (_elems eq) (M.insert val root)
  return root

-- given a reference, find a reference to the root of its equivalence class.
-- This function performs path compression
findRoot :: Ord a => NRef s a -> ST s (NRef s a)
findRoot ref = do
  node <- readSTRef (_ref ref)
  case node of
    Root {} -> return ref
    Node {_parent = refToParent} -> do
      refToRoot <- findRoot refToParent
      if refToRoot /= refToParent then
        writeSTRef (_ref ref) node{_parent = refToRoot} >> return refToRoot
      else return refToRoot

-- combine two equivalence classes, merging the smaller into the larger
union :: Ord a => NRef s a -> NRef s a -> ST s ()
union refX refY = do
  refToRootX <- findRoot refX
  refToRootY <- findRoot refY
  when (refToRootX /= refToRootY) $ do
    (Root vx wx) <- readSTRef (_ref refToRootX)
    (Root vy wy) <- readSTRef (_ref refToRootY)
    if (wx >= wy) then do
      writeSTRef (_ref refToRootY) (Node vy refToRootX)
      writeSTRef (_ref refToRootX) (Root vx (wx + wy))
    else do
      writeSTRef (_ref refToRootX) (Node vx refToRootY)
      writeSTRef (_ref refToRootY) (Root vy (wx + wy))

-- Are these two references pointing to the same root?
equivalent :: Ord a => NRef s a -> NRef s a -> ST s Bool
equivalent x y = (==) <$> findRoot x <*> findRoot y

getRef :: Ord a => Equiv s a -> a -> ST s (Maybe (NRef s a))
getRef eq x = do
  m <- readSTRef (_elems eq)
  return $ M.lookup x m

equate :: Ord a => Equiv s a -> a -> a -> ST s ()
equate eq x y = do
  rx <- (maybe (singleton eq x) return) =<< (getRef eq x)
  ry <- (maybe (singleton eq y) return) =<< (getRef eq y)
  union rx ry

-- Equality
-- ========

congruent :: Equiv s Term -> Term -> Term -> ST s Bool
congruent eq a b = do
  equate eq a b
  let go = congruent eq
  case (a,b) of
    (All _ _ _ h b, All _ _ _ h' b') -> (&&) <$> go h h' <*> go b b'
    (Lam _ _ b,     Lam _ _ b')      -> go b b'
    (App _ f a,     App _ f' a')     -> (&&) <$> go f f' <*> go a a'
    (Let _ x b,     Let _ x' b')     -> (&&) <$> go x x' <*> go b b'
    (Ann _ t x,     Ann _ t' x')     -> (&&) <$> go t t' <*> go x x'
    _                                -> return False

