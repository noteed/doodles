{-# LANGUAGE ViewPatterns, FlexibleInstances, TypeSynonymInstances #-}
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
-- appearing in the type signature of baseInt is related
-- to the Float value (of type TypeRep) in the constructed
-- node. Maybe I could use TH to generate some of this stuff.
--
-- 'usage' : in ghci : doDot ex1
--
module Graph where

import Control.Monad.State
import qualified Data.IntMap as IM
import Data.List
import Data.Typeable
import Data.Dynamic

true = True
false = False

int = typeOf (undefined :: Int)
float = typeOf (undefined :: Float)

myTypeOf t = go (typeOf t) []
  where
    go t acc =
      if null xs
        then (reverse acc,t)
        else go (last xs) (head xs : acc)
      where xs = typeRepArgs t

-- A reference is simply an Int. But to gain some type-safety
-- the reference are wrapped (below).
type Ref = Int

-- A typed reference.
data TRef a = TRef Ref

type RInt = TRef Int
type RFloat = TRef Float

type Rank = Int

-- e.g. Op Int "plus" [a,b] [c] means the node Plus depends on a and b (the parents)
-- and c depends on it (c is a child of Plus).
data Node = Base TypeRep String [Ref]
          | Op TypeRep String  [Ref] [Ref] Rank -- parents, children
  deriving Show

info (Base _ i _) = i
info (Op _ i _ _ _) = i

rank :: Node -> Rank
rank (Base _ _ _) = 0
rank (Op _ _ _ _ rk) = rk

parents (Base _ _ _) = []
parents (Op _ _ _ p _) = p

children (Base _ _ c) = c
children (Op _ _ _ c _) = c

data G = G { nodes :: IM.IntMap Node, nextName :: Ref }
  deriving Show

type N a = State G (TRef a)

emptyGraph = G IM.empty 0

graph :: N a -> IM.IntMap Node
graph = nodes . (flip execState emptyGraph)

alist = IM.toList . graph

byrank g = sortBy (\a b -> (rank . snd) a `compare` (rank . snd) b) (alist g)

grouped g = groupBy (\a b -> (rank . snd) a == (rank . snd) b) (byrank g)

-- labels
dotOne1 (r,node) = "n" ++ show r ++ " [label=\"" ++ info node ++ "\"]\n"
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

instance Show (N w) where
  show g = show $ execState g emptyGraph

instance Eq (N w) where
  a == b = error "TODO: Eq instance for (N w)"

instance (Typeable n, Num n) => Num (N n) where
  (+) = lift2 (+) "add"
  (*) = lift2 (*) "mul"
  signum = lift1 signum "signumf"
  abs = lift1 abs "abs"
  fromInteger = (base undefined) . show

instance (Typeable n, Fractional n) => Fractional (N n) where
  (/) = lift2 (/) "divf"
  recip = lift1 recip "recip"
  fromRational = (base undefined) . show . fromRational

addChild' c (Base t info cs) = Base t info (c:cs)
addChild' c (Op t info ps cs rk) = Op t info ps (c:cs) rk

-- Create a node (and give it automatically a name).
mkNode n = do
  i <- gets nextName
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }
  return i

-- Add a node named (refenced by) i.
addNode i n = do
  ns <- gets nodes
  put $ G { nodes = IM.insert i n ns, nextName = i + 1 }

-- Add c as a child to the node n.
addChild c n = do
  ns <- gets nodes
  g <- get
  put $ g { nodes = IM.adjust (addChild' c) n ns }

base :: Typeable a => a -> String -> N a
base v info = mkNode (Base (typeOf v) info []) >>= return . TRef

baseInt = base (undefined::Int)

baseFloat = base (undefined::Float)

lift1 :: (Typeable a, Typeable b) => (a -> b) -> String -> (N a -> N b)
lift1 f name = \a -> do
  TRef n1 <- a
  rk <- gets (rank . (IM.! n1) . nodes)
  n <- gets nextName
  addChild n n1
  addNode n (Op (typeOf $ f undefined) name [n1] [] (rk + 1))
  return (TRef n)

lift2 :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> String -> (N a -> N b -> N c)
lift2 f name = \a b -> do
  TRef n1 <- a
  TRef n2 <- b
  rk1 <- gets (rank . (IM.! n1) . nodes)
  rk2 <- gets (rank . (IM.! n2) . nodes)
  n <- gets nextName
  addChild n n1
  addChild n n2
  addNode n (Op (typeOf $ f undefined undefined) name [n1,n2] [] (max rk1 rk2 + 1))
  return (TRef n)

foo = lift2 f "foo"
  where f :: Int -> Float -> String
        f x s = "hello"

milliseconds = baseInt "milliseconds"

ex1 = (milliseconds + 45) `foo` 55.6

ex1' = execState ex1 emptyGraph


