{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingVia #-}
module FormalityCore where

import           Data.List           hiding (all, find, union)
import qualified Data.Map.Strict     as M
import           Data.Maybe
import           Data.Foldable       hiding (all, find)
import           Data.Bits           ((.&.), xor, shiftR, shiftL, Bits)
import           Data.Word
import           Data.Char           (ord)

import qualified Data.Sequence as Seq
import           Data.Sequence (Seq(..), (<|), (|>))

import Control.Monad.ST
import Data.STRef
import qualified Data.IntMap.Strict         as IM
import Data.IntMap.Strict (IntMap)

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

import           Control.Applicative
import           Control.Monad

import Debug.Trace

import           Prelude             hiding (all, mod)

-- Formality-Core types
-- ====================

type Name = String
type Done = Bool   -- Annotation flag
type Eras = Bool   -- Erasure mark

-- Formality-Core parsed terms
data TermP
  = VarP Int                         -- Variable
  | RefP Name                        -- Reference
  | TypP                             -- Type type
  | AllP Eras Name Name TermP TermP  -- Forall
  | LamP Eras Name TermP             -- Lambda
  | AppP Eras TermP TermP            -- Application
  | LetP Name TermP TermP            -- Let expression
  | AnnP TermP TermP                 -- Type annotation
  deriving Show

-- Formality-Core parsed definitions
data DefP = DefP { _nameP :: Name, _typeP :: TermP, _termP :: TermP } 
  deriving Show

newtype ModuleP = ModuleP (M.Map Name DefP) deriving Show

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

string :: String -> Parser String
string str = Parser $ \i -> case stripPrefix str i of
  Just i' -> Just (i', str)
  Nothing -> Nothing

-- Formality-Core parser
-- =====================

-- is a space character
isSpace :: Char -> Bool
isSpace c = c `elem` " \t\n"

-- is a name character
isName :: Char -> Bool
isName c = c `elem` (['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "_" ++ ".")

-- consume whitespace
whitespace :: Parser ()
whitespace = takeWhile1P isSpace >> return ()

-- parse // line comments
lineComment :: Parser ()
lineComment =
  choice
    [ string "//" >> takeWhileP (/= '\n') >> string "\n" >> return ()
    , string "--" >> takeWhileP (/= '\n') >> return ()
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

-- parse an optional character
opt :: Char -> Parser Bool
opt c = isJust <$> optional (string (c:[]))

-- parse a valid name, non-empty
nam :: Parser String
nam = takeWhile1P isName

-- Parses a parenthesis, `(<term>)`
par :: [Name] -> Parser TermP
par vs = string "(" >> space >> trm vs <* space <* string ")"

-- Parses a dependent function type, `(<name> : <term>) => <term>`
-- optionally with a self-type: `<name>(<name> : <term>) => <term>`
all :: [Name] -> Parser TermP
all vs = do
  s <- maybe "" id <$> (optional nam)
  e <- (string "(" >> return False) <|> (string "<" >> return True)
  n <- maybe "" id <$> (optional nam <* space)
  t <- sym ":" >> trm (s : vs) <* space
  (if e then sym ">" else sym ")")
  b <- sym "->" >> trm (n : s : vs)
  return $ AllP e s n t b

-- Parses a dependent function value, `(<name>) => <term>`
lam :: [Name] -> Parser TermP
lam vs = do
  e <- (string "(" >> return False) <|> (string "<" >> return True)
  n <- maybe "" id <$> (space >> (optional nam) <* space)
  (if e then sym ">" else sym ")")
  b <- trm (n : vs)
  return $ LamP e n b

-- Parses the type of types, `Type`
typ :: Parser TermP
typ = string "Type" >> return TypP

-- Parses variables, `<name>`
var :: [Name] -> Parser TermP
var vs = (\n -> maybe (RefP n) VarP (elemIndex n vs)) <$> nam

let_ :: [Name] -> Parser TermP
let_ vs = do
  n <- sym "let" >> nam <* space
  x <- sym "=" >> trm vs <* space <* optional (sym ";")
  t <- trm (n:vs)
  return $ LetP n x t

-- Parses a sequence of applications:
-- `<term>(<term>)...(<term>)` or `<term> | (<term>); | ... | (<term>);`.
-- note that this parser differs from the JS parser due to Haskell's laziness
app :: [Name] -> TermP -> Parser TermP
app vs f = foldl (\t (a,e) -> AppP e t a) f <$> (some $ arg vs)
  where
  arg vs = choice
    [ do
      e <- (string "(" >> return False) <|> (string "<" >> return True)
      t <- space >> trm vs <* space <* (if e then string ">" else string ")")
      return (t,e)
    , (,False) <$> (space >> sym "|" >> trm vs <* space <* string ";")
    ]

-- Parse non-dependent function type `<term> -> <term>`
arr :: [Name] -> TermP -> Parser TermP
arr vs bind = do
  body <- space >> sym "->" >> trm ("":"":vs)
  return $ AllP False "" "" (fromTerm $ shift (toTerm bind) 1 0) body

-- Parses an annotation, `<term> :: <term>`
ann :: [Name] -> TermP -> Parser TermP
ann vs x = do
  space >> sym "::"
  t <- trm vs
  return $ AnnP x t

-- Parses a term
trm :: [Name] -> Parser TermP
trm vs = do
  t <- choice [all vs, lam vs, let_ vs, typ, var vs, par vs]
  t <- app vs t <|> return t
  t <- arr vs t <|> return t
  ann vs t <|> return t

parseTerm :: String -> Maybe TermP
parseTerm str = snd <$> runParser (trm []) str

-- Parses a definition
def :: Parser DefP
def = DefP <$> (nam <* space) <*> (sym ":" >> trm []) <*> (space >> trm [])

-- Parses a module
mod :: Parser ModuleP
mod = ModuleP . M.fromList <$> fmap (\d -> (_nameP d, d)) <$> defs
  where
   defs = (space >> many (def <* space))

parseMod :: String -> IO (Maybe (String, ModuleP))
parseMod file = do
  a <- readFile file
  return $ runParser mod a

unsafeParseMod :: String -> IO Module
unsafeParseMod file = do
  a <- readFile file
  case runParser mod a of
    Nothing    -> error "didn't parse"
    Just (_,x) -> return $ toModule x

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

-- Hashing
-- =============

newtype Hash = Hash {_word32 :: Word32} deriving (Eq,Num,Bits,Show) via Word32

mix64 :: Word64 -> Word64
mix64 h =
  let h1     = xor h (shiftR h 33)
      h2     = h1 * 0xff51afd7ed558ccd
      h3     = xor h2 (shiftR h2 33)
      h4     = h3 * 0xc4ceb9fe1a85ec53
   in xor h4 (shiftR h4 33)

hashTwo :: Hash -> Hash -> Hash
hashTwo (Hash x) (Hash y) = Hash $ fromIntegral pos
  where
     pre = (fromIntegral x) `xor` (shiftL (fromIntegral y) 32)
     pos = shiftR (mix64 $ pre) 32

instance Semigroup Hash where
  (<>) = hashTwo

instance Monoid Hash where
  mempty = 0
  mappend = (<>)

hashStr :: String -> Hash
hashStr str = foldMap (fromIntegral . ord) str

-- Formality-Core Terms
data Term
  = Var { _hash :: Hash, _indx :: Int}
  | Ref { _hash :: Hash, _name :: Name }
  | Typ { _hash :: Hash }
  | All { _hash :: Hash, _eras :: Eras, _self :: Name
        , _name :: Name, _bind :: Term, _body :: Term
        }
  | Lam { _hash :: Hash, _eras :: Eras, _name :: Name, _body :: Term}
  | App { _hash :: Hash, _eras :: Eras, _func :: Term, _argm :: Term}
  | Let { _hash :: Hash, _name :: Name, _expr :: Term, _body :: Term}
  | Ann { _hash :: Hash, _done :: Bool, _term :: Term, _type :: Term}
  deriving Show


-- Stringification, or, pretty-printing
-- ===================================

find :: [a] -> Int -> Maybe a
find xs i
  | i < 0 || i >= length xs = Nothing
  | otherwise = Just $ xs !! i

--instance Show Term where
--  show = pretty []

pretty :: [Name] -> Term -> String
pretty vs t = case t of
    Var _ i         -> case find vs i of 
      Just x  -> x -- ++ "#" ++ show i
      Nothing -> "#" ++ show i
    Ref _ ""        -> "#Ref"
    Ref _ n         -> n
    Typ _          -> "Type"
    All _ e s "" h b -> cat [s,era e [go (s:vs) h]," -> ",go ("":s:vs) b]
    All _ e s n h b  -> cat [s,era e [n," : ",go (s:vs) h]," -> ",go (n:s:vs) b]
    Lam _ e n b     -> cat [era e [n]," ",go (n:vs) b]
    App _ e f a     -> case f of
      (Lam _ _ _ _)     -> cat ["(", go vs f,")", era e [go vs a]]
      (All _ _ _ _ _ _) -> cat ["(", go vs f,")", era e [go vs a]]
      f                 -> cat [go vs f,era e [go vs a]]
    Let _ n x b     -> cat ["let ", n," = ",go vs x,"; ", go (n:vs) b]
    Ann _ d x y     -> cat ["(",go vs x,") :: (",go vs y, ")"]
  where
    go = pretty
    cat = concat
    --ite e x y = if e then x else y

    era e x = if e then cat ["<",cat x,">"] else cat ["(",cat x,")"]
    go :: [Name] -> Term -> String

--instance Show Def where
--  show (Def n t d) = concat [n," : ", show t, "\n", show d]
--
--instance Show Module where
--  show (Module m)  = go $ snd <$> (M.toList m)
--    where
--      go []     = ""
--      go [d]    = show d
--      go (d:ds) = show d ++ "\n\n" ++ go ds


mkVar i         = Var (1 <> fromIntegral i) i
mkRef n         = Ref (2 <> hashStr n) n
mkTyp           = Typ (3 <> 0)
mkAll e s n h b = All (4 <> _hash h <> _hash b) e s n h b
mkLam e n b     = Lam (5 <> _hash b) e n b
mkApp e f a     = App (6 <> _hash f <> _hash a) e f a
mkLet n x b     = Let (7 <> _hash x <> _hash b) n x b
mkAnn d x t     = Ann (8 <> _hash x <> _hash t) d x t


toTerm :: TermP -> Term
toTerm t = let go = toTerm in case t of
  VarP i         -> mkVar i
  RefP n         -> mkRef n
  TypP           -> mkTyp
  AllP e s n h b -> mkAll e s n (go h) (go b)
  LamP e n b     -> mkLam e n (go b)
  AppP e f a     -> mkApp e (go f) (go a)
  LetP n x b     -> mkLet n (go x) (go b)
  AnnP x t       -> mkAnn False (go x) (go t) 

fromTerm :: Term -> TermP
fromTerm t = let go = fromTerm in case t of
  Var _ i         -> VarP i
  Ref _ n         -> RefP n
  Typ _           -> TypP
  All _ e s n h b -> AllP e s n (go h) (go b)
  Lam _ e n b     -> LamP e n (go b)
  App _ e f a     -> AppP e (go f) (go a)
  Let _ n x b     -> LetP n (go x) (go b)
  Ann _ d x t     -> AnnP (go x) (go t)

-- Formality-Core definitions
data Def = Def
  { _defName :: Name
  , _defHash :: Hash
  , _defType :: Term
  , _defTerm :: Term
  } deriving Show

mkDef :: Name -> Term -> Term -> Def
mkDef n t d = Def n (_hash t <> _hash d) t d

toDef :: DefP -> Def
toDef (DefP n t d) = mkDef n (toTerm t) (toTerm d)

-- Formality-Core Module
data Module = Module
  { _modHash :: Hash
  , _defs :: M.Map Name Def 
  } deriving Show

emptyMod = Module 0 M.empty

mkModule :: Map Name Def -> Module
mkModule defs = Module (foldMap _defHash defs) defs

toModule :: ModuleP -> Module
toModule (ModuleP defs) = mkModule (toDef <$> defs)

-- Substitution
-- ============

-- in a term, shift all indices above a depth
shift :: Term -> Int -> Int -> Term
shift term 0 _ = term
shift term inc dep = case term of
  Var _ indx                     ->
    if indx < dep
    then mkVar indx
    else mkVar (indx + inc)
  Ref _ name                     -> mkRef name
  Typ _                          -> mkTyp
  All _ eras self name bind body ->
    mkAll eras self name
      (shift bind inc (dep + 1))
      (shift body inc (dep + 2))
  Lam _ eras name body           -> mkLam eras name
      (shift body inc (dep + 1))
  App _ eras func argm           ->
    mkApp eras
      (shift func inc dep)
      (shift argm inc dep)
  Let _ name expr body           ->
    mkLet name
      (shift expr inc dep)
      (shift body inc (dep + 1))
  Ann _ done expr typ            ->
    mkAnn done
      (shift expr inc dep)
      (shift typ  inc dep)

-- in a term, substitute a value for an index at a certain depth
subst :: Term -> Term -> Int -> Term
subst term val dep = case term of
  Var _ indx                     -> case compare indx dep of
    LT -> term
    EQ -> val
    GT -> mkVar (indx - 1)
  Ref _ name                     -> mkRef name
  Typ _                          -> mkTyp
  All _ eras self name bind body ->
    mkAll eras self name
      (subst bind (shift val 1 0) (dep + 1))
      (subst body (shift val 2 0) (dep + 2))
  Lam _ eras name body           ->
    mkLam eras name
      (subst body (shift val 1 0) (dep + 1))
  App _ eras func argm           ->
    mkApp eras
      (subst func val dep)
      (subst argm val dep)
  Let _ name expr body           ->
    mkLet name
      (subst expr val dep)
      (subst body (shift val 1 0) (dep + 1))
  Ann _ done expr typ            -> 
    mkAnn done
      (subst expr val dep)
      (subst typ val dep)

-- Evaluation
-- ==========

-- Higher Order Abstract Syntax (HOAS) terms
data TermH
  = VarH Int
  | RefH Name
  | TypH
  | AllH Eras Name Name (TermH -> TermH) (TermH -> TermH -> TermH)
  | LamH Eras Name (TermH -> TermH)
  | AppH Eras TermH TermH
  | LetH Name TermH (TermH -> TermH)

-- convert lower-order terms to higher order terms
toHighOrder :: Term -> TermH
toHighOrder term = go term [] 0
  where
    go :: Term -> [TermH] -> Int -> TermH
    go term vars depth = case term of
      Var _ indx                     -> case find vars indx of
        Nothing     -> VarH (depth - indx - 1)
        Just value  -> value
      Ref _ name                     -> RefH name
      Typ _                          -> TypH
      All _ eras self name bind body ->
        AllH eras self name
          (\s -> go bind (s:vars) (depth + 1))
          (\s x -> go body (x:s:vars) (depth + 2))
      Lam _ eras name body           ->
        if eras
        then go (subst body (mkRef "<erased>") 0) vars depth
        else LamH False name (\x -> go body (x:vars) (depth + 1))
      App _ eras func argm           ->
        if eras
        then go func vars depth
        else AppH False (go func vars depth) (go argm vars depth)
      Let _ name expr body           ->
        LetH name
          (go expr vars depth)
          (\x -> go body (x:vars) (depth + 1))
      Ann _ done expr typ            -> go expr vars depth

-- convert higher-order terms to lower-order terms
toLowOrder :: TermH -> Term
toLowOrder term = go term 0
  where
    go :: TermH -> Int -> Term
    go term depth = case term of
      VarH indx         -> mkVar (depth - indx - 1)
      RefH name         -> mkRef name
      TypH              -> mkTyp
      AllH eras self name bind body ->
        mkAll eras self name
          (go (bind $ VarH depth) (depth + 1))
          (go (body (VarH depth) (VarH $ depth + 1)) (depth + 2))
      LamH eras name body           ->
        mkLam eras name
          (go (body $ VarH depth) (depth + 1))
      AppH eras func argm           ->
        mkApp eras
          (go func depth)
          (go argm depth)
      LetH name expr body           ->
        mkLet name
          (go expr depth)
          (go (body $ VarH depth) (depth + 1))

---- lower-order interpreter
--evalTerm :: Term -> Module -> Term
--evalTerm term mod = go term
--  where
--  go :: Term -> Term
--  go t = case t of
--    Lam h e n b     -> mkLam e n (go b)
--    App h e f a     -> case go f of
--      Lam h e n b -> go (subst a 0 b)
--      f           -> mkApp e f (go a)
--    Ann h d t x     -> go x
--    Let h n x b     -> subst x 0 b
--    Ref h n         -> case (deref n mod) of
--      Ref h' m -> go (deref n mod)
--      x        -> go x
--    _               -> term


-- HOAS reduction
reduceHighOrder :: TermH -> Module -> TermH
reduceHighOrder term mod = go term
  where
    go :: TermH -> TermH
    go term = case term of
      VarH indx                     -> VarH indx
      RefH name                     -> case M.lookup name (_defs mod) of
        Just x                      -> go (toHighOrder (_defTerm x))
        Nothing                     -> RefH name
      TypH                          -> TypH
      AllH eras self name bind body -> AllH eras self name bind body
      LamH eras name body           -> LamH False name body
      AppH eras func argm           -> case go func of
        LamH _ _ funcBody -> go (funcBody argm)
        func'             -> AppH False func' (go argm)
      LetH name expr body           -> go (body expr)

-- HOAS normalization
normalizeHighOrder :: TermH -> Module -> TermH
normalizeHighOrder term mod = go term
  where
    go :: TermH -> TermH
    go t = case (reduceHighOrder term mod) of
      VarH indx                     -> VarH indx
      RefH name                     -> RefH name
      TypH                          -> TypH
      AllH eras self name bind body ->
        AllH eras self name
          (\s -> go $ bind s)
          (\s x -> go $ body s x)
      LamH eras name body           ->
        LamH eras name
          (\x -> go $ body x)
      AppH eras func argm           ->
        AppH eras
          (go func)
          (go argm)
      LetH name expr body           ->
        LetH name
          (go expr)
          (\x -> go $ body x)

-- convert term to higher order and reduce
reduce :: Term -> Module -> Term
reduce term mod = toLowOrder $ reduceHighOrder (toHighOrder term) mod

-- convert term to higher order and normalize
normalize :: Term -> Module -> Term
normalize term mod = toLowOrder $ normalizeHighOrder (toHighOrder term) mod

-- Union Find
-- ===========

-- An lightweight implementation of Tarjan's Union-Find algorithm for hashable
-- types. This is a port of the /equivalence/ package and uses mutable
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
--
-- The integer values in the Val type are intended for use with some `a -> Int`
-- hashing function

type Val = Int

-- A reference to a node
newtype NodeRef s = NodeRef { _ref :: STRef s (Node s) } deriving Eq

-- A Node is either root or a link
data Node s
  = Root {_value :: Val, _weight :: Int}
  | Node {_value :: Val, _parent :: NodeRef s}

-- An equivalence relation is a reference to a map of elements to node references
data Equiv s = Equiv {_elems :: STRef s (IntMap (NodeRef s))}

-- A new equivalence relation
newEquiv :: ST s (Equiv s)
newEquiv = Equiv <$> (newSTRef IM.empty)

-- create a new class in a relation with a value as root
singleton :: Equiv s -> Val -> ST s (NodeRef s)
singleton eq val = do
  root <- NodeRef <$> newSTRef (Root {_value = val, _weight = 1})
  modifySTRef (_elems eq) (IM.insert val root)
  return root

-- given a reference, find a reference to the root of its equivalence class.
-- This function performs path compression
findRoot :: NodeRef s -> ST s (NodeRef s)
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
union :: NodeRef s -> NodeRef s -> ST s ()
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

getNodeRef :: Equiv s -> Val -> ST s (Maybe (NodeRef s))
getNodeRef eq x = do
  m <- readSTRef (_elems eq)
  return $ IM.lookup x m

equate :: Equiv s -> Val -> Val -> ST s ()
equate eq x y = do
  rx <- (maybe (singleton eq x) return) =<< (getNodeRef eq x)
  ry <- (maybe (singleton eq y) return) =<< (getNodeRef eq y)
  union rx ry

-- Are these two values the same?
isEquivalent :: Equiv s -> Val -> Val -> ST s Bool
isEquivalent eq a b = do
  elems <- readSTRef (_elems eq)
  case (IM.lookup a elems, IM.lookup b elems) of
    (Just x,Just y) -> (==) <$> findRoot x <*> findRoot y
    _               -> equate eq a b >> return (a == b)


-- Equality
-- ========

mkBound :: Int -> Term
mkBound x = Ref (2 <> hashStr ("%" ++ (show x))) ("%" ++ (show x))

bindFreeVars :: Term -> Int -> Term
bindFreeVars term initialDepth = go term 0
  where
    go :: Term -> Int -> Term
    go term depth = case term of
      Var _ indx                     ->
        if indx < depth
        then mkVar indx
        else mkBound (initialDepth - 1 - (indx - depth))
      Ref _ name                     -> mkRef name
      Typ _                          -> mkTyp
      All _ eras self name bind body ->
        mkAll eras self name
          (go bind (depth + 1))
          (go body (depth + 2))
      Lam _ eras name body           ->
        mkLam eras name
          (go body (depth + 1))
      App _ eras func argm           ->
        mkApp eras
          (go func depth)
          (go argm depth)
      Let _ name expr body           ->
        mkLet name
          (go expr depth)
          (go body (depth + 1))
      Ann _ done expr typ            ->
        mkAnn done
          (go expr depth)
          (go typ  depth)

congruent :: Equiv s -> Term -> Term -> ST s Bool
congruent equiv a b = do
  let getHash = fromIntegral . _word32 . _hash
  i <- isEquivalent equiv (getHash a) (getHash b)
  if i then return True
  else do
    case (a,b) of
      (All _ aEras aSelf _ aBind aBody, All _ bEras bSelf _ bBind bBody) -> do
        congEras <- return $ aEras == bEras
        congSelf <- return $ aSelf == bSelf
        congBind <- congruent equiv aBind bBind
        congBody <- congruent equiv aBody bBody
        return $ congEras && congSelf && congBind && congBody
      (Lam _ aEras _ aBody,     Lam _ bEras _ bBody)                     -> do
        congEras <- return $ aEras == bEras
        congBody <- congruent equiv aBody bBody
        return $ congEras && congBody
      (App _ aEras aFunc aArgm,     App _ bEras bFunc bArgm)             -> do
        congEras <- return $ aEras == bEras
        congFunc <- congruent equiv aFunc bFunc
        congArgm <- congruent equiv aArgm bArgm
        return $ congEras && congFunc && congArgm
      (Let _ _ aExpr aBody,     Let _ _ bExpr bBody)                     -> do
        congExpr <- congruent equiv aExpr bExpr
        congBody <- congruent equiv aBody bBody
        return $ congExpr && congBody
      (Ann _ _ aExpr _,     Ann _ _ bExpr _)                             -> do
        congruent equiv aExpr bExpr
      _                                                                  -> do
        return False

equal :: Term -> Term -> Module -> Int -> Bool
equal a b mod dep = runST $ (newEquiv >>= (\e -> go e vis))
  where
    vis     = Seq.singleton (bindFreeVars a dep, bindFreeVars b dep, dep)
    getHash = fromIntegral . _word32 . _hash

    go :: Equiv s -> Seq (Term,Term,Int) -> ST s Bool
    go _  Empty              = return True
    go equiv ((a,b,depth) :<| vs) = do
      let a' = reduce a mod
      let b' = reduce b mod
      id <- congruent equiv a' b'
      equate equiv (getHash a)  (getHash a')
      equate equiv (getHash b)  (getHash b')
      equate equiv (getHash a') (getHash b')
      if id then (go equiv vs)
      else case (a',b') of
        (All _ aEras aSelf _ aBind aBody, All _ bEras bSelf _ bBind bBody) -> do
          if (aEras /= bEras || aSelf /= bSelf) then return False
          else do
            let aBind'  = subst aBind  (mkBound $ depth + 0) 0
            let bBind'  = subst bBind  (mkBound $ depth + 0) 0
            let aBody'  = subst aBody  (mkBound $ depth + 1) 1
            let aBody'' = subst aBody' (mkBound $ depth + 0) 0
            let bBody'  = subst bBody  (mkBound $ depth + 1) 1
            let bBody'' = subst bBody' (mkBound $ depth + 0) 0
            let vs'     = vs  :|> (aBind' , bBind' , depth + 1)
            let vs''    = vs' :|> (aBody'', bBody'', depth + 2)
            go equiv vs''
        (Lam _ aEras _ aBody, Lam _ bEras _ bBody)                         -> do
          if (aEras /= bEras) then return False
          else do
            let aBody'  = subst aBody (mkBound $ depth + 0) 0
            let bBody'  = subst bBody (mkBound $ depth + 0) 0
            let vs'     = vs :|> (aBody', bBody', depth + 1)
            go equiv vs'
        (App _ aEras aFunc aArgm, App _ bEras bFunc bArgm)                 -> do
          if (aEras /= bEras) then return False
          else do
            let vs'  = vs  :|> (aFunc, bFunc, depth)
            let vs'' = vs' :|> (aArgm, bArgm, depth)
            go equiv vs''
        (Let _ _ aExpr aBody,     Let _ _ bExpr bBody)                     -> do
          let aBody' = subst aBody (mkBound $ depth + 0) 0
          let bBody' = subst bBody (mkBound $ depth + 0) 0
          let vs'    = vs  :|> (aExpr , bExpr , depth)
          let vs''   = vs' :|> (aBody', bBody', depth + 1)
          go equiv vs''
        (Ann _ _ aExpr _, Ann _ _ bExpr _)                                 -> do
          let vs'    = vs :|> (aExpr, bExpr, depth)
          go equiv vs'
        _                                                                  -> do
          return False

data TypeError = TypeError String deriving Show


infer :: Term -> Module -> [Term] -> [Name] -> Either TypeError Term
infer term mod ctx nam = do
  let term' = pretty nam term
  -- traceM ("infer " ++ term')
  -- traceM ("ctx: " ++ prettyCtx ctx nam)
  case term of
    Var _ indx                     -> do
      case find ctx indx of
        Nothing    -> Left $ TypeError "Unbound variable"
        Just value -> do
          -- traceM ("solve " ++ term' ++ " : " ++ (pretty nam (shift value (indx + 1) 0)))
          -- traceM ("-----")
          return $ shift value (indx + 1) 0
    Ref _ name                     -> do
      case M.lookup name (_defs mod) of
        Nothing  -> Left $ TypeError "Undefined Reference"
        Just def -> return $ _defType def
    Typ _                          -> do
      -- traceM ("infer Typ")
      -- traceM ("solve " ++ term' ++ " : " ++ (pretty nam mkTyp))
      -- traceM ("-----")
      return $ mkTyp
    App _ eras func argm           -> do
      funcTyp <- (\x -> reduce x mod) <$> infer func mod ctx nam
      case funcTyp of
        All _ funcTypEras funcTypSelf funcTypName funcTypBind funcTypBody -> do
          let expeTyp = subst funcTypBind func 0
          check argm expeTyp mod ctx nam
          let termTyp1 = funcTypBody
          let termTyp2 = subst termTyp1 (shift func 1 0) 1
          let termTyp3 = subst termTyp2 (shift argm 0 0) 0
          if (eras /= funcTypEras)
          then (Left $ TypeError "Mismatched erasure")
          else do
          -- traceM ("solve " ++ term' ++ " : " ++ (pretty (funcTypName:funcTypSelf:nam) termTyp3))
          -- traceM ("-----")
          (return termTyp3)
        _ -> Left $ TypeError "Non-function application"
    Let _ name expr body           -> do
      exprType <- infer expr mod ctx nam
      let bodyNam = name:nam
      let bodyCtx = exprType:ctx
      bodyType <- infer body mod bodyCtx bodyNam
      -- traceM ("solve " ++ term' ++ " : " ++ pretty bodyNam (subst bodyType expr 0))
      -- traceM ("-----")
      return $ subst bodyType expr 0
    All _ eras self name bind body -> do
      let selfType = mkAnn True term mkTyp
      let bindCtx  = selfType:ctx
      let bindNam  = self:nam
      bindTyp <- check bind mkTyp mod bindCtx bindNam
      let bodyCtx  = bind:selfType:ctx
      let bodyNam  = name:self:nam
      check body mkTyp mod bodyCtx bodyNam
      -- traceM ("solve " ++ term' ++ " : " ++ (pretty nam mkTyp))
      -- traceM ("-----")
      return mkTyp
    Ann _ done expr typ            -> do
      if done
      then do
        -- traceM ("solve " ++ term' ++ " : " ++ (pretty nam typ))
        -- traceM ("-----")
        return typ
      else check expr typ mod ctx nam
    _                              -> do
      Left $ TypeError "Can't infer type"

check :: Term -> Term -> Module -> [Term] -> [Name] -> Either TypeError Term
check term typ mod ctx nam = do
  -- traceM ("check: " ++ pretty nam term)
  -- traceM ("typed: " ++ pretty nam typ)
  -- traceM ("ctx: " ++ prettyCtx ctx nam)
  -- traceM ("=====")
  let typv = reduce typ mod
  case term of
    Lam _ eras name body -> do
      case typv of
        All _ typvEras _ typvName typvBind typvBody -> do
          let selfTyp = mkAnn True typv mkTyp
          let bindTyp = subst typvBind term 0
          let bodyTyp = subst typvBody (shift term 1 0) 1
          let bodyNam = name:nam
          let bodyCtx = bindTyp:ctx
          if (eras /= typvEras)
          then Left $ TypeError "Type mismatch"
          else do
            check body bodyTyp mod bodyCtx bodyNam
            return typ
        _                                           -> do
          Left $ TypeError "Lambda has a non-function type"
    _                                -> do
      infr <- infer term mod ctx nam
      -- traceM ("infr: " ++ pretty nam infr)
      if (equal typ infr mod (length ctx)) then return $ Typ 3
      else Left $ TypeError $
        intercalate "\n" 
          [ "Unexpected type: "
          , "Expected: ", pretty nam typ
          , "Inferred: ", pretty nam infr
          , "Inferred on: ", pretty nam term
          , "Context: ", intercalate "\n" $ show <$> zip nam ctx
          ]

prettyCtx :: [Term] -> [Name] -> String
prettyCtx ctx nam = go ctx nam []
  where
    go []     _      ls = "[" ++ intercalate ", " (reverse ls) ++ "]"
    go (c:cs) (n:ns) ls = go cs ns ((n ++ " : " ++ pretty ns c):ls)


checkDef :: Module -> Def -> IO ()
checkDef m (Def nam _ typ term) = do
  putStrLn $ concat ["CHECKING: ",nam]
  let x = check term typ m [] [] 
  case x of
    Left (TypeError s) -> do
      putStrLn ("ERROR: " ++ nam)
      putStrLn s >> return ()
    Right _            -> do 
      --putStrLn ("GOOD: " ++ nam)
      --print typ
      return ()

checkName :: Module -> Name -> Either TypeError Term
checkName m n = case (_defs m) M.! n of
  (Def _ _ typ term) -> check term typ m [] []

checkMod :: String -> IO ()
checkMod file = do
  a <- readFile file
  case runParser mod a of
   Nothing    -> putStrLn "Parse Error"
   Just (x,m) -> do
     when (x /= "") (putStrLn "expected EOF")
     let mod = toModule m
     sequence (checkDef mod <$> (_defs mod))
     return ()
