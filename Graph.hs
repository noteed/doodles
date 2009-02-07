{-# LANGUAGE ViewPatterns, FlexibleInstances, TypeSynonymInstances, NoMonomorphismRestriction #-}
-- 2009.01.08
-- 2009.02.02
-- autumnae
--
-- The graph is made of nodes named/referenced by Int's.
-- Nodes have a field denoting their type, but otherwise
-- have all the same type (i.e. Node).
--
-- To gain some safety from Haskell's type system,
-- function to create and combine nodes are typed :
-- nodes have the same type (so they can be put inside
-- a Map) but their reference are typed.
--
-- But nothing enforces the relationship between the type
-- of the typed references and the value denoting that type
-- inside the Node. See for instance how the Float type
-- appearing in the type signature of (constant float) is related
-- to the Float value (of type TypeRep) in the constructed
-- node. Maybe I could use TH to generate some of this stuff.
--
-- 'usage' : in ghci : doDot ex1
-- or : ghc Graph.hs -e 'doDot ex1' | dot -Tsvg -oex1.svg
--
module Graph where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.List
import Data.Typeable
import Data.Dynamic

true = True
false = False

int = undefined :: Int
float = undefined :: Float

-- Thanks to Ross Mellgren on the Haskell-Cafe mailing list.
argsOf :: TypeRep -> [TypeRep]
argsOf ty
  | typeRepTyCon ty == funTyCon = let ([x,y]) = typeRepArgs ty in x : argsOf y
  | otherwise = [ty] -- 'return' type
  where funTyCon :: TyCon
        funTyCon = mkTyCon "->"

myTypeOf :: Typeable a => a -> [TypeRep]
myTypeOf = argsOf . typeOf

-- A reference is simply an Int. But to gain some type-safety
-- the reference are wrapped (below).
type Ref = Int

-- A typed reference.
data TRef a = TRef Ref
  deriving Show

type RInt = TRef Int
type RFloat = TRef Float

type Rank = Int

-- e.g. Op ([Int,Int],Int) "plus" [a,b] [c] means the node Plus depends
-- on a and b (the parents) and c depends on it (c is a child of Plus).
-- Furthermore the type of the parents should match with the one of the Op.
data Node = Cst TypeRep  String [Ref]
          | In  TypeRep  String [Ref]               -- children
          | Out TypeRep  String [Ref] Rank         -- parents
          | Op [TypeRep] String [Ref] [Ref] Rank -- parents, children
  deriving Show

isCst (Cst _ _ _) = True
isCst _ = False
isIn (In _ _ _) = True
isIn _ = False
isOut (Out _ _ _ _) = True
isOut _ = False
isOp (Op _ _ _ _ _) = True
isOp _ = False

info (Cst _ i _) = i
info (In _ i _) = i
info (Out _ i _ _) = i
info (Op _ i _ _ _) = i

rank :: Node -> Rank
rank (Cst _ _ _) = 0
rank (In _ _ _) = 0
rank (Out _ _ _ rk) = rk
rank (Op _ _ _ _ rk) = rk

parents (Cst _ _ _) = []
parents (In _ _ _) = []
parents (Out _ _ p _) = []
parents (Op _ _ _ p _) = p

children (Cst _ _ c) = c
children (In _ _ c) = c
children (Out _ _ _ _) = []
children (Op _ _ _ c _) = c

typeRep (Cst t _ _) = t
typeRep (In t _ _) = t
typeRep (Out t _ _ _) = t
typeRep (Op t _ _ _ _) = last t

data G = G { nodes :: IM.IntMap Node, nextName :: Ref }
  deriving Show

type N a = State G (TRef a)

emptyGraph = G IM.empty 0

graph :: State G a -> IM.IntMap Node
graph = nodes . (flip execState emptyGraph)

alist = IM.toList . graph

-- Returns all the nodes sorted by their rank (so Inputs and Constans come first).
byrank g = sortBy (\a b -> (rank . snd) a `compare` (rank . snd) b) (alist g)

-- Groups all the nodes according to their rank (with Inputs and
-- Constants coming first).
grouped g = groupBy (\a b -> (rank . snd) a == (rank . snd) b) (byrank g)

-- Gives the list of node which depends on the node (referenced by n).
below g n = tail $ below' n
  where below' n = let n' = l n in (n,n') : concatMap below' (children n')
        l n = (graph g) IM.! n

-- nodes
dotOne1 (r,node) = "n" ++ show r ++ " [" ++
  (concat $ intersperse ", " $ ["label=\"" ++ info node ++ "\""] ++ attr node)
  ++ "]\n"
  where attr n | isCst n = ["color=grey"]
               | isIn n = ["color=cyan"]
               | isOut n = ["color=orange"]
               | otherwise = []
dotRank1 = concatMap dotOne1
dot1 = (concatMap dotRank1) . grouped

-- arcs
dotOne2 (r,node) = concatMap (\c -> "n" ++ show r ++ " -> n" ++ show c ++ "\n") (children node)
dotRank2 = concatMap dotOne2
dot2 = (concatMap dotRank2) . grouped

doDot g = do
  putStrLn "digraph G {"
  putStr $ dot1 g
  putStrLn ""
  putStr $ dot2 g
  putStrLn "}"

instance Show (State G a) where
  show g = show $ execState g emptyGraph

instance Eq (N w) where
-- TODO special case for commutative operations.
  a == b = same g1 g2 (n1,n2)
   where
    (TRef n1, nodes -> g1) = runState a emptyGraph
    (TRef n2, nodes -> g2) = runState b emptyGraph

eq a b = same g1 g2 (n1,n2)
   where
    (TRef n1, nodes -> g1) = runState a emptyGraph
    (TRef n2, nodes -> g2) = runState b emptyGraph

same g1 g2 (n1,n2) =
  case (g1 IM.! n1) of
    Cst t1 i1 _     -> case (g2 IM.! n2) of
                         Cst t2 i2 _ -> t1 == t2 && i1 == i2
                         otherwise   -> False
    In t1 i1 _      -> case (g2 IM.! n2) of
                         In t2 i2 _ -> t1 == t2 && i1 == i2
                         otherwise   -> False
    Out t1 i1 p1 _  -> case (g2 IM.! n2) of
                         Out t2 i2 p2 _ -> t1 == t2 && i1 == i2 && length p1 == length p2 && and (map (same g1 g2) (zip p1 p2))
                         otherwise   -> False
    Op t1 i1 p1 _ _ -> case (g2 IM.! n2) of
                         Op t2 i2 p2 _ _ -> t1 == t2 && i1 == i2 && length p1 == length p2 && and (map (same g1 g2) (zip p1 p2))
                         otherwise       -> False

instance (Typeable n, Num n) => Num (N n) where
  (+) = lift2 (+) "+"
  (*) = lift2 (*) "*"
  signum = lift1 signum "signumf"
  abs = lift1 abs "abs"
  fromInteger = (constant undefined) . show

instance (Typeable n, Fractional n) => Fractional (N n) where
  (/) = lift2 (/) "/"
  recip = lift1 recip "recip"
  fromRational = (constant undefined) . show . fromRational

addChild' c (Cst t info cs) = Cst t info (c:cs)
addChild' c (In t info cs) = In t info (c:cs)
addChild' c (Op t info ps cs rk) = Op t info ps (c:cs) rk

-- Create a node (and give it automatically a name).
mkNode n = do
  i <- gets nextName
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }
  return i

-- Add c as a child to the node n.
addChild c n = do
  ns <- gets nodes
  g <- get
  put $ g { nodes = IM.adjust (addChild' c) n ns }

constant :: Typeable a => a -> String -> N a
constant v info = mkNode (Cst (typeOf v) info []) >>= return . TRef

input :: Typeable a => a -> String -> N a
input v info = mkNode (In (typeOf v) info []) >>= return . TRef

output info a = do
  TRef n1 <- a
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Out (typeRep node) info [n1] (rank node + 1))
  addChild n n1
  return (TRef n)

out info (TRef n1) = do
  node <- gets ((IM.! n1) . nodes)
  n <- mkNode (Out (typeRep node) info [n1] (rank node + 1))
  addChild n n1
  return (TRef n)

lift1 :: (Typeable a, Typeable b) => (a -> b) -> String -> (N a -> N b)
lift1 f name = \a -> do
  r1 <- a
  op1 f name r1

-- test for similar subgraph (not every nodes are checked, just the two
-- added nodes are tested against each other, but it works).
lift2' :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2' f name = \a b ->
  if a `eq` b
   then do
    TRef n1 <- a
    rk1 <- gets (rank . (IM.! n1) . nodes)
    n <- mkNode (Op (myTypeOf f) name [n1,n1] [] (rk1 + 1))
    addChild n n1
    return (TRef n)
   else do
    r1 <- a
    r2 <- b
    op2 f name r1 r2
-- no test
lift2 :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2 f name = \a b -> do
  r1 <- a
  r2 <- b
  op2 f name r1 r2

op1 :: (Typeable a, Typeable b) => (a -> b) -> String -> TRef a -> N b
op1 f name (TRef n1) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  n <- mkNode (Op (myTypeOf f) name [n1] [] (rk1 + 1))
  addChild n n1
  return (TRef n)

op2 :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> String -> TRef a -> TRef b -> N c
op2 f name (TRef n1) (TRef n2) = do
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- mkNode (Op (myTypeOf f) name [n1,n2] [] (max rk1 rk2 + 1))
  addChild n n1
  addChild n n2
  return (TRef n)

add = op2 (+) "+"

foo = lift2 f "foo"
f :: Int -> Float -> String
f x s = "hello"

milliseconds = input int "milliseconds"

ex1 = output "hey" $ (milliseconds + 45) `foo` (55.6 * 1.2)

ex1' = execState ex1 emptyGraph

-- The main problem of this approch is showed
-- by doDot ex2 : the subgraph constructed by a
-- is not shared. (It's just like a is a little
-- program that is run twice by the + combinator.)
-- If it was a real little language, a would be a
-- lookup on a symbol table, not two 'commands'.
--
-- A solution is to add a node to the graph if
-- there isn't yet such a node. I.e. every new node
-- is checked against every existing node. Maybe it
-- would be expensive but it could find redondant
-- node even if they were not initially shared.
ex2 = output "yah" $ a + a
  where a = (milliseconds + 12 + 46)
(+++) = lift2' (+) "+check"
ex3 = output "yah-shared" $ a +++ a
  where a = (milliseconds + 12 + 46)

-- no problem to discover sharing here.
ex4 = do
  m <- input int "milliseconds"
  a <- add m m
  out "out" a
  return ()
